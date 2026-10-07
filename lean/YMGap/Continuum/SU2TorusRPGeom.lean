/-
# Torus RP geometry (c): the time-reflection Θ of the periodic torus `N = 2M`

Time is coordinate `x0`. `Θ` acts on vertices by `t ↦ 1 − t (mod N)` and fixes the two cut pairs `{0,1}` and `{M,M+1}`.
On links:
* a spatial link `(v,d)` goes to `(Θv, d)`;
* a temporal link `(v,x0)` goes to `(Θ(v+e0), x0)`, i.e. the orientation is reversed, so its variable becomes `U*`.
Each link and plaquette gets a side: `pos` (times `1..M`), `neg`, or `cross` (temporal links at times `0` and `M`,
and time-plaquettes based there). Proved, for all box vertices:
* `rt_invol`, `refl_invol`: Θ is an involution on links.
* `side_refl`: Θ swaps `pos` and `neg` and keeps `cross`; `cross_fixed`: each crossing link is Θ-fixed.
* `plaq_pos` / `plaq_neg`: every link of a `pos` (`neg`) plaquette is `pos` (`neg`).
* `plaq_cross`: a crossing plaquette (base time `a ∈ {0, M}`, plane `(x0, d)`) has exactly two crossing temporal
  links, plus one spatial link on each side, and these two are Θ-images of each other.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (assembly (d) remains).
-/

import YMGap.Continuum.SU2PlaqSupport

namespace YMGap.Continuum.SU2TorusRPGeom

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2PlaqSupport (plaqLinks)

inductive Side | pos | neg | cross
  deriving DecidableEq

def Side.swap : Side → Side
  | .pos => .neg | .neg => .pos | .cross => .cross

variable (M : Nat)

/-- Time reflection `t ↦ 1 − t mod 2M`. -/
def rt (a : Nat) : Nat := if a = 0 then 1 else if a = 1 then 0 else 2 * M + 1 - a

def rv : Z4Vertex → Z4Vertex | (a, b, c, d) => (rt M a, b, c, d)

def reflLink : Z4Link → Z4Link
  | (v, .x0) => (rv M (tAdd (2 * M) v .x0), .x0)
  | (v, d) => (rv M v, d)

def tSide (a : Nat) : Side := if a = 0 ∨ a = M then .cross else if a < M then .pos else .neg
def sSide (a : Nat) : Side := if 1 ≤ a then (if a ≤ M then .pos else .neg) else .neg

def linkSide : Z4Link → Side
  | (v, .x0) => tSide M v.1
  | (v, _) => sSide M v.1

def plaqSide (p : Z4Plaq) : Side :=
  match (dirsOf p.2).1 with
  | .x0 => tSide M p.1.1
  | _ => sSide M p.1.1

variable {M}

theorem ws {a : Nat} (ha : a < 2 * M) : wrapSucc (2 * M) a = if a + 1 = 2 * M then 0 else a + 1 := by
  unfold wrapSucc; split
  · rename_i h; rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- Split every `if` and every in-box `wrapSucc`, then close the arithmetic. -/
macro "geo" : tactic => `(tactic| ((repeat' (first
    | (simp only [Nat.not_le, Nat.not_lt, not_or] at *)
    | (simp (disch := omega) only [ws, if_pos, if_neg, Side.swap])
    | split | intro)) <;>
  (try simp only [Side.swap, reduceCtorEq, and_true, true_and, and_self, imp_false, not_false_eq_true, true_or,
    or_true, not_true_eq_false, false_or, or_false, false_and, and_false] at *) <;>
  (try (first | rfl | (exfalso; omega) | omega | (exact ⟨rfl, rfl⟩) | (exact ⟨by omega, nofun⟩) | (constructor <;> omega)))))

variable (hM : 1 ≤ M)
include hM

theorem rt_lt {a : Nat} (ha : a < 2 * M) : rt M a < 2 * M := by unfold rt; geo

theorem rt_invol {a : Nat} (ha : a < 2 * M) : rt M (rt M a) = a := by unfold rt; geo

theorem refl_invol (ℓ : Z4Link) (h : InBox (2 * M) ℓ.1) : reflLink M (reflLink M ℓ) = ℓ := by
  obtain ⟨⟨a, b, c, d⟩, e⟩ := ℓ
  have ha : a < 2 * M := h.1
  cases e <;> simp only [reflLink, rv, tAdd, Prod.mk.injEq, and_true, rt_invol hM ha]
  have h1 := wrapSucc_lt (show 0 < 2 * M by omega) a
  rw [ws (rt_lt hM h1), ws ha]
  unfold rt; geo

theorem side_refl (ℓ : Z4Link) (h : InBox (2 * M) ℓ.1) : linkSide M (reflLink M ℓ) = (linkSide M ℓ).swap := by
  obtain ⟨⟨a, b, c, d⟩, e⟩ := ℓ
  have ha : a < 2 * M := h.1
  cases e <;> simp only [reflLink, rv, tAdd, linkSide, tSide, sSide, rt] <;> geo

theorem cross_fixed (ℓ : Z4Link) (h : InBox (2 * M) ℓ.1) (hc : linkSide M ℓ = .cross) : reflLink M ℓ = ℓ := by
  obtain ⟨⟨a, b, c, d⟩, e⟩ := ℓ
  have ha : a < 2 * M := h.1
  cases e <;> simp only [linkSide, tSide, sSide, reflLink, rv, tAdd, rt, Prod.mk.injEq, and_true] at hc ⊢ <;> revert hc <;> geo

theorem plaq_pos (p : Z4Plaq) (h : InBox (2 * M) p.1) (hp : plaqSide M p = .pos) :
    ∀ ℓ ∈ plaqLinks (2 * M) p, linkSide M ℓ = .pos := by
  obtain ⟨⟨a, b, c, d⟩, P⟩ := p
  have ha : a < 2 * M := h.1
  cases P <;> simp only [plaqSide, dirsOf, tSide, sSide, plaqLinks, tAdd, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, linkSide] at hp ⊢ <;> revert hp <;> geo

theorem plaq_neg (p : Z4Plaq) (h : InBox (2 * M) p.1) (hp : plaqSide M p = .neg) :
    ∀ ℓ ∈ plaqLinks (2 * M) p, linkSide M ℓ = .neg := by
  obtain ⟨⟨a, b, c, d⟩, P⟩ := p
  have ha : a < 2 * M := h.1
  cases P <;> simp only [plaqSide, dirsOf, tSide, sSide, plaqLinks, tAdd, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, linkSide] at hp ⊢ <;> revert hp <;> geo

/-- A crossing plaquette with plane `(x0, d)` at base `v`: its links `(v,x0)` and `(v+e_d, x0)` are crossing; the
spatial links `(v,d)` and `(v+e0, d)` lie on opposite sides and are Θ-images of each other. -/
theorem plaq_cross (v : Z4Vertex) (P : Z4Plane) (h : InBox (2 * M) v) (hp : plaqSide M (v, P) = .cross) :
    (dirsOf P).1 = .x0 ∧ linkSide M (v, .x0) = .cross ∧ linkSide M (tAdd (2 * M) v (dirsOf P).2, .x0) = .cross ∧
      reflLink M (tAdd (2 * M) v .x0, (dirsOf P).2) = (v, (dirsOf P).2) ∧
      linkSide M (v, (dirsOf P).2) ≠ .cross := by
  obtain ⟨a, b, c, d⟩ := v
  have ha : a < 2 * M := h.1
  cases P <;> simp only [plaqSide, dirsOf, tSide, sSide, tAdd, linkSide, reflLink, rv, rt, Prod.mk.injEq,
      and_true, true_and] at hp ⊢ <;> revert hp <;> geo


end YMGap.Continuum.SU2TorusRPGeom

#print axioms YMGap.Continuum.SU2TorusRPGeom.refl_invol
#print axioms YMGap.Continuum.SU2TorusRPGeom.side_refl
#print axioms YMGap.Continuum.SU2TorusRPGeom.cross_fixed
#print axioms YMGap.Continuum.SU2TorusRPGeom.plaq_pos
#print axioms YMGap.Continuum.SU2TorusRPGeom.plaq_neg
#print axioms YMGap.Continuum.SU2TorusRPGeom.plaq_cross
#print axioms YMGap.Continuum.SU2TorusRPGeom.rt_lt
#print axioms YMGap.Continuum.SU2TorusRPGeom.rt_invol
#print axioms YMGap.Continuum.SU2TorusRPGeom.ws

