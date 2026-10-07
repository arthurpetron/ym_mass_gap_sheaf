/-
# Torus RP (d9c): the plaquette-index shape of an actual crossing plaquette

For a crossing plaquette `(v, P)` (plane `(x0, d)`, base time `0` or `M`), `plaqIdx` is
`[idx (v,x0), idx (v+e0,d), idx (v+e_d,x0), idx (v,d)]`. At cut `0` the positive spatial link is `ℓ = (v+e0,d)` with
`Θℓ = (v,d)` (shape of `rpk_lay0`); at cut `M` it is `ℓ = (v,d)` with `Θℓ = (v+e0,d)` (shape of `rpk_layM`).
Both crossing links sit at time `v.1`, and `ℓ` is spatial and `pos`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPSplitTK
import YMGap.Continuum.SU2TorusRPThetaTK

namespace YMGap.Continuum.SU2TorusRPCrossGeom

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusRPGeom (reflLink linkSide plaqSide Side tSide sSide rt rv ws)
open YMGap.Continuum.SU2TorusRPSplitTK (plaqIdx)
open YMGap.Continuum.SU2TorusRPThetaTK (isT)

variable {M : Nat} (hM : 1 ≤ M) (L : List Z4Link)
include hM

theorem cross_shape0 (v : Z4Vertex) (P : Z4Plane) (h : InBox (2 * M) v) (hp : plaqSide M (v, P) = .cross)
    (h0 : v.1 = 0) :
    plaqIdx L (2 * M) (v, P) = [L.idxOf (v, .x0), L.idxOf (tAdd (2 * M) v .x0, (dirsOf P).2),
      L.idxOf (tAdd (2 * M) v (dirsOf P).2, .x0), L.idxOf (reflLink M (tAdd (2 * M) v .x0, (dirsOf P).2))] ∧
    (tAdd (2 * M) v (dirsOf P).2, Dir4.x0).1.1 = 0 ∧ isT (dirsOf P).2 = false ∧
    linkSide M (tAdd (2 * M) v .x0, (dirsOf P).2) = .pos ∧
    linkSide M (v, .x0) = .cross ∧ linkSide M (tAdd (2 * M) v (dirsOf P).2, .x0) = .cross := by
  obtain ⟨a, b, c, d⟩ := v
  have ha : a < 2 * M := h.1
  simp only at h0; subst h0
  cases P <;> simp only [plaqSide, dirsOf, tSide, sSide, plaqIdx, tAdd, linkSide, reflLink, rv, rt, isT,
      Prod.mk.injEq, and_true, true_and] at hp ⊢ <;> revert hp <;> geo

theorem cross_shapeM (v : Z4Vertex) (P : Z4Plane) (h : InBox (2 * M) v) (hp : plaqSide M (v, P) = .cross)
    (hMv : v.1 = M) :
    plaqIdx L (2 * M) (v, P) = [L.idxOf (v, .x0), L.idxOf (reflLink M (v, (dirsOf P).2)),
      L.idxOf (tAdd (2 * M) v (dirsOf P).2, .x0), L.idxOf (v, (dirsOf P).2)] ∧
    (tAdd (2 * M) v (dirsOf P).2, Dir4.x0).1.1 = M ∧ isT (dirsOf P).2 = false ∧
    linkSide M (v, (dirsOf P).2) = .pos ∧
    linkSide M (v, .x0) = .cross ∧ linkSide M (tAdd (2 * M) v (dirsOf P).2, .x0) = .cross := by
  obtain ⟨a, b, c, d⟩ := v
  have ha : a < 2 * M := h.1
  simp only at hMv; subst hMv
  cases P <;> simp only [plaqSide, dirsOf, tSide, sSide, plaqIdx, tAdd, linkSide, reflLink, rv, rt, isT,
      Prod.mk.injEq, and_true, true_and] at hp ⊢ <;> revert hp <;> geo <;> (try rw [show 2 * a + 1 - a = a + 1 by omega])

end YMGap.Continuum.SU2TorusRPCrossGeom

#print axioms YMGap.Continuum.SU2TorusRPCrossGeom.cross_shape0
#print axioms YMGap.Continuum.SU2TorusRPCrossGeom.cross_shapeM
