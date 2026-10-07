/-
# Torus RP (d9d): every actual crossing plaquette is RPK after the layout split

If `C` contains every in-box crossing link, `P` every in-box `pos` link, and `P` is in the box, then each in-box
crossing plaquette `q` gives `RPK a (Ctw a layT (imgTK … (chImg .direct layChain) q))`. This is the per-crossing
input of `torus_rp_master`, from `cross_shape0/M` + `rpk_lay0/M`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPLayoutCross
import YMGap.Continuum.SU2TorusRPCrossGeom

namespace YMGap.Continuum.SU2TorusRPCrossPlaq

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusRPGeom (reflLink linkSide plaqSide Side tSide sSide refl_invol)
open YMGap.Continuum.SU2TorusRPSplitChain (chImg)
open YMGap.Continuum.SU2TorusRPSplitTK (imgTK)
open YMGap.Continuum.SU2TorusRPLayoutChain (layChain)
open YMGap.Continuum.SU2TorusRPLayoutT (layT)
open YMGap.Continuum.SU2TorusRPCore (RPK)
open YMGap.Continuum.SU2TorusRPCrossC (Ctw)

theorem cross_time {M : Nat} (v : Z4Vertex) (P : Z4Plane) (hp : plaqSide M (v, P) = .cross) :
    v.1 = 0 ∨ v.1 = M := by
  obtain ⟨a, b, c, d⟩ := v
  cases P <;> simp only [plaqSide, dirsOf, tSide, sSide] at hp ⊢ <;> revert hp <;> geo

variable {M : Nat} (hM : 1 ≤ M) (P C : List Z4Link) (hnd : (P ++ C ++ P.map (reflLink M)).Nodup)
  (ha : 1 ≤ P.length + C.length)
  (hCcov : ∀ ℓ : Z4Link, InBox (2 * M) ℓ.1 → linkSide M ℓ = .cross → ℓ ∈ C)
  (hPcov : ∀ ℓ : Z4Link, InBox (2 * M) ℓ.1 → linkSide M ℓ = .pos → ℓ ∈ P)
  (hPbox : ∀ x ∈ P, InBox (2 * M) x.1)

include hM hCcov hPcov hPbox in
theorem rpk_cross_plaq {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (hC : C.Nodup) (v : Z4Vertex) (Pl : Z4Plane)
    (hv : InBox (2 * M) v) (hp : plaqSide M (v, Pl) = .cross) :
    RPK (P.length + C.length) (Ctw (P.length + C.length) (layT (P ++ C ++ P.map (reflLink M)))
      (imgTK (P ++ C ++ P.map (reflLink M)) (2 * M) β K (chImg .direct (layChain M P C hnd ha)) (v, Pl))) := by
  have hN : 0 < 2 * M := by omega
  have hinj : ∀ ℓ, ∀ x ∈ P, reflLink M x = reflLink M ℓ → InBox (2 * M) ℓ.1 → x = ℓ := fun ℓ x hx he hb => by
    rw [← refl_invol hM x (hPbox x hx), he, refl_invol hM ℓ hb]
  rcases cross_time v Pl hp with h0 | hMv
  · obtain ⟨hidx, hs2, hT, hpos, hc1, hc2⟩ :=
      YMGap.Continuum.SU2TorusRPCrossGeom.cross_shape0 hM (P ++ C ++ P.map (reflLink M)) v Pl hv hp h0
    have hb : InBox (2 * M) (tAdd (2 * M) v .x0) := tAdd_inBox hN hv _
    exact YMGap.Continuum.SU2TorusRPLayoutCross.rpk_lay0 M P C hnd ha hβ K hC (v, Pl) _ _ _
      (hCcov _ hv hc1) (hCcov _ (tAdd_inBox hN hv _) hc2) (hPcov _ hb hpos) hT
      (fun x hx he => hinj _ x hx he hb) h0 hs2 hidx
  · obtain ⟨hidx, hs2, hT, hpos, hc1, hc2⟩ :=
      YMGap.Continuum.SU2TorusRPCrossGeom.cross_shapeM hM (P ++ C ++ P.map (reflLink M)) v Pl hv hp hMv
    exact YMGap.Continuum.SU2TorusRPLayoutCross.rpk_layM M P C hnd ha hβ K hC (v, Pl) _ _ _
      (hCcov _ hv hc1) (hCcov _ (tAdd_inBox hN hv _) hc2) (hPcov _ hv hpos) hT
      (fun x hx he => hinj _ x hx he hv) (show v.1 ≠ 0 by omega) (by rw [hs2]; omega) hidx

end YMGap.Continuum.SU2TorusRPCrossPlaq

#print axioms YMGap.Continuum.SU2TorusRPCrossPlaq.cross_time
#print axioms YMGap.Continuum.SU2TorusRPCrossPlaq.rpk_cross_plaq
