/-
# Torus RP (d9e): box/side facts for Θ on links and for mirrored plaquettes

* `refl_box`: Θ keeps links in the box.
* `mir_box`, `mir_side`: the mirror of an in-box `pos` plaquette is in the box and `neg`.
* `plaqIdx_eq`: `plaqIdx` is `idxOf` mapped over `plaqLinks`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPSplitTK
import YMGap.Continuum.SU2TorusRPThetaProd

namespace YMGap.Continuum.SU2TorusRPMirGeom

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusRPGeom (reflLink linkSide plaqSide Side tSide sSide rt rv ws)
open YMGap.Continuum.SU2TorusRPSplitTK (plaqIdx)
open YMGap.Continuum.SU2TorusRPThetaTK (isT)
open YMGap.Continuum.SU2TorusRPThetaProd (mir)
open YMGap.Continuum.SU2PlaqSupport (plaqLinks)

theorem plaqIdx_eq (L : List Z4Link) (N : Nat) (p : Z4Plaq) : plaqIdx L N p = (plaqLinks N p).map L.idxOf := rfl

variable {M : Nat} (hM : 1 ≤ M)
include hM

theorem refl_box (ℓ : Z4Link) (h : InBox (2 * M) ℓ.1) : InBox (2 * M) (reflLink M ℓ).1 := by
  obtain ⟨⟨a, b, c, d⟩, e⟩ := ℓ
  obtain ⟨ha, hb, hc, hd⟩ := h
  have h1 := wrapSucc_lt (show 0 < 2 * M by omega) a
  cases e
  · exact ⟨YMGap.Continuum.SU2TorusRPGeom.rt_lt hM h1, hb, hc, hd⟩
  all_goals exact ⟨YMGap.Continuum.SU2TorusRPGeom.rt_lt hM ha, hb, hc, hd⟩

theorem mir_side (p : Z4Plaq) (h : InBox (2 * M) p.1) (hp : plaqSide M p = .pos) :
    InBox (2 * M) (mir M p).1 ∧ plaqSide M (mir M p) = .neg := by
  obtain ⟨⟨a, b, c, d⟩, P⟩ := p
  obtain ⟨ha, hb, hc, hd⟩ := h
  have h1 := wrapSucc_lt (show 0 < 2 * M by omega) a
  have r1 := YMGap.Continuum.SU2TorusRPGeom.rt_lt hM h1
  have r2 := YMGap.Continuum.SU2TorusRPGeom.rt_lt hM ha
  cases P <;> simp only [mir, dirsOf, isT, if_true, if_false, Bool.false_eq_true, tAdd, rv] at r1 ⊢ <;>
    refine ⟨⟨by assumption, hb, hc, hd⟩, ?_⟩ <;>
    (simp only [plaqSide, dirsOf, tSide, sSide, rt] at hp ha ⊢; clear r1 r2 h1 hb hc hd; (try rw [ws ha]); revert hp; geo)

end YMGap.Continuum.SU2TorusRPMirGeom

#print axioms YMGap.Continuum.SU2TorusRPMirGeom.refl_box
#print axioms YMGap.Continuum.SU2TorusRPMirGeom.mir_side
#print axioms YMGap.Continuum.SU2TorusRPMirGeom.plaqIdx_eq
