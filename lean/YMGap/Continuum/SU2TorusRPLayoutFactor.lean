/-
# Torus RP (d9f): the factorisation `hfac` on the layout, for actual torus plaquettes

With `C` ⊇ in-box crossing links, `P` ⊇ in-box `pos` links, `P` in the box, and `ps ~ pos ++ mir pos ++ cross` with
every `pos` plaquette in the box and `pos`, the image product splits as `Wp · Θ_H Wp · ∏_cross imgTK`, where
`Wp = ∏_pos TK` (`lay_factor`), from `split_factor`, `lay_HD`, `imgTK_noncross`, `mir_side`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPCrossPlaq
import YMGap.Continuum.SU2TorusRPMirGeom

namespace YMGap.Continuum.SU2TorusRPLayoutFactor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2HaarAlgebra (PE)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2PlaqSupport (plaqLinks)
open YMGap.Continuum.SU2TorusRPGeom (reflLink linkSide plaqSide Side refl_invol side_refl plaq_pos plaq_neg)
open YMGap.Continuum.SU2TorusRPSplitChain (chImg)
open YMGap.Continuum.SU2TorusRPSplitTK (imgTK)
open YMGap.Continuum.SU2TorusRPLayoutChain (layChain)
open YMGap.Continuum.SU2TorusRPLayoutT (layT)
open YMGap.Continuum.SU2TorusRPThetaProd (mir)
open YMGap.Continuum.SU2TorusRPHalfSwap (thetaH)

theorem plaqLinks_box {N : Nat} (hN : 0 < N) (p : Z4Plaq) (h : InBox N p.1) :
    ∀ ℓ ∈ plaqLinks N p, InBox N ℓ.1 := by
  intro ℓ hℓ
  simp only [plaqLinks, List.mem_cons, List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | rfl | rfl | rfl
  · exact h
  · exact tAdd_inBox hN h _
  · exact tAdd_inBox hN h _
  · exact h

variable {M : Nat} (hM : 1 ≤ M) (P C : List Z4Link) (hnd : (P ++ C ++ P.map (reflLink M)).Nodup)
  (ha : 1 ≤ P.length + C.length)
  (hPcov : ∀ ℓ : Z4Link, InBox (2 * M) ℓ.1 → linkSide M ℓ = .pos → ℓ ∈ P)
  (hPbox : ∀ x ∈ P, InBox (2 * M) x.1)

include hM hPbox in
theorem hinjP (ℓ : Z4Link) (hb : InBox (2 * M) ℓ.1) : ∀ x ∈ P, reflLink M x = reflLink M ℓ → x = ℓ :=
  fun x hx he => by rw [← refl_invol hM x (hPbox x hx), he, refl_invol hM ℓ hb]

include hM hPcov hPbox in
theorem lay_factor (β : Q') (K : Nat) (ps pos cross : List Z4Plaq)
    (hperm : ps.Perm (pos ++ pos.map (mir M) ++ cross))
    (hposP : ∀ p ∈ pos, InBox (2 * M) p.1 ∧ plaqSide M p = .pos) :
    PE ((P.length + C.length) + (P.length + C.length))
      (prodPoly (imgTK (P ++ C ++ P.map (reflLink M)) (2 * M) β K (chImg .direct (layChain M P C hnd ha))) ps)
      (polyMul (polyMul (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (P ++ C ++ P.map (reflLink M)) (2 * M) β K) pos)
          (thetaH (P.length + C.length) (layT (P ++ C ++ P.map (reflLink M)))
            (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (P ++ C ++ P.map (reflLink M)) (2 * M) β K) pos)))
        (prodPoly (imgTK (P ++ C ++ P.map (reflLink M)) (2 * M) β K (chImg .direct (layChain M P C hnd ha))) cross)) := by
  have hN : 0 < 2 * M := by omega
  have linkP : ∀ p ∈ pos, ∀ ℓ ∈ plaqLinks (2 * M) p, InBox (2 * M) ℓ.1 ∧ ℓ ∈ P := fun p hp ℓ hℓ => by
    have hb := plaqLinks_box hN p (hposP p hp).1 ℓ hℓ
    exact ⟨hb, hPcov ℓ hb (plaq_pos hM p (hposP p hp).1 (hposP p hp).2 ℓ hℓ)⟩
  refine YMGap.Continuum.SU2TorusRPSplitFactor.split_factor hM _ _ _ β K _ ps pos cross hperm
    (fun p hp => ⟨(hposP p hp).1.1, fun ℓ hℓ => YMGap.Continuum.SU2TorusRPLayoutT.lay_HD M P C hnd ℓ
      (linkP p hp ℓ hℓ).2 (hinjP hM P hPbox ℓ (linkP p hp ℓ hℓ).1)⟩) ?_
  intro q hq
  refine YMGap.Continuum.SU2TorusRPLayoutCross.imgTK_noncross M P C hnd ha K q ?_
  rw [YMGap.Continuum.SU2TorusRPMirGeom.plaqIdx_eq]
  intro b hb
  obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hb
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl ⟨ℓ, (linkP q hq ℓ hℓ).2, rfl⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    obtain ⟨hmb, hms⟩ := YMGap.Continuum.SU2TorusRPMirGeom.mir_side hM p (hposP p hp).1 (hposP p hp).2
    have hb := plaqLinks_box hN _ hmb ℓ hℓ
    have hneg := plaq_neg hM _ hmb hms ℓ hℓ
    have hb' := YMGap.Continuum.SU2TorusRPMirGeom.refl_box hM ℓ hb
    have hpos' : linkSide M (reflLink M ℓ) = .pos := by rw [side_refl hM ℓ hb, hneg]; rfl
    have hℓ' := hPcov _ hb' hpos'
    obtain ⟨-, h2⟩ := YMGap.Continuum.SU2TorusRPLayout.lay_pos P C (reflLink M) hnd _ hℓ'
      (hinjP hM P hPbox _ hb')
    rw [refl_invol hM ℓ hb] at h2
    right; rw [h2]; exact Nat.le_add_left _ _

end YMGap.Continuum.SU2TorusRPLayoutFactor

#print axioms YMGap.Continuum.SU2TorusRPLayoutFactor.plaqLinks_box
#print axioms YMGap.Continuum.SU2TorusRPLayoutFactor.lay_factor
