/-
# Torus RP (d9s): `mir` is an involution on box plaquettes and maps `neg` to `pos`

* `mir_eq`: `mir p` is based at the Θ-image of the link `(p.1, first direction)`.
* `mir_invol`: `mir (mir p) = p` for in-box `p`.
* `mir_side_neg`: the mirror of an in-box `neg` plaquette is in the box and `pos`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPMirGeom
import YMGap.Continuum.SU2TorusRPLayoutT

namespace YMGap.Continuum.SU2TorusRPMirInv

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusRPGeom (reflLink plaqSide Side tSide sSide rt rv ws refl_invol)
open YMGap.Continuum.SU2TorusRPThetaTK (isT)
open YMGap.Continuum.SU2TorusRPThetaProd (mir)

theorem mir_eq (M : Nat) (p : Z4Plaq) : mir M p = ((reflLink M (p.1, (dirsOf p.2).1)).1, p.2) := by
  obtain ⟨⟨a, b, c, d⟩, P⟩ := p
  cases P <;> rfl

variable {M : Nat} (hM : 1 ≤ M)
include hM

theorem mir_invol (p : Z4Plaq) (h : InBox (2 * M) p.1) : mir M (mir M p) = p := by
  rw [mir_eq, mir_eq]
  obtain ⟨v, P⟩ := p
  have hd := YMGap.Continuum.SU2TorusRPLayoutT.refl_dir M (v, (dirsOf P).1)
  have e : ((reflLink M (v, (dirsOf P).1)).1, (dirsOf P).1) = reflLink M (v, (dirsOf P).1) :=
    Prod.ext rfl hd.symm
  dsimp only
  rw [e, refl_invol hM _ h]

theorem mir_side_neg (p : Z4Plaq) (h : InBox (2 * M) p.1) (hp : plaqSide M p = .neg) :
    InBox (2 * M) (mir M p).1 ∧ plaqSide M (mir M p) = .pos := by
  obtain ⟨⟨a, b, c, d⟩, P⟩ := p
  obtain ⟨ha, hb, hc, hd⟩ := h
  have h1 := wrapSucc_lt (show 0 < 2 * M by omega) a
  have r1 := YMGap.Continuum.SU2TorusRPGeom.rt_lt hM h1
  have r2 := YMGap.Continuum.SU2TorusRPGeom.rt_lt hM ha
  cases P <;> simp only [mir, dirsOf, isT, if_true, if_false, Bool.false_eq_true, tAdd, rv] at r1 ⊢ <;>
    refine ⟨⟨by assumption, hb, hc, hd⟩, ?_⟩ <;>
    (simp only [plaqSide, dirsOf, tSide, sSide, rt] at hp ha ⊢; clear r1 r2 h1 hb hc hd; (try rw [ws ha]); revert hp; geo)

end YMGap.Continuum.SU2TorusRPMirInv

#print axioms YMGap.Continuum.SU2TorusRPMirInv.mir_invol
#print axioms YMGap.Continuum.SU2TorusRPMirInv.mir_side_neg
