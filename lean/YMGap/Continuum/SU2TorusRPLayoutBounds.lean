/-
# Torus RP (d9i): index bound and `hWp` on the layout; `torus_rp_layout'`

* `mem_lay`: with the covers, every in-box link lies in `L = P ++ C ++ Θ P`.
* `hps_lay`: every in-box plaquette has all its link indices `< 2a`.
* `hWp_lay`: `Sup a (∏_pos T_K)` for in-box `pos` plaquettes.
* `torus_rp_layout'`: `torus_rp_layout` with `hps`, `hWp` discharged (`ps` in the box). Remaining: `hXfix`, `hsup`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPSupTK

namespace YMGap.Continuum.SU2TorusRPLayoutBounds

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2HaarAlgebra (PE)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2PlaqSupport (plaqLinks)
open YMGap.Continuum.SU2TorusRPSplitTK (plaqIdx)
open YMGap.Continuum.SU2TorusRPCore (Sup)
open YMGap.Continuum.SU2TorusRPHaar (conjSel)
open YMGap.Continuum.SU2TorusRPGeom (reflLink linkSide plaqSide Side refl_invol side_refl plaq_pos)
open YMGap.Continuum.SU2TorusRPLayoutChain (layChain)
open YMGap.Continuum.SU2TorusRPLayoutT (layT)
open YMGap.Continuum.SU2TorusRPThetaProd (mir)
open YMGap.Continuum.SU2TorusRPHalfSwap (halfSwap)
open YMGap.Continuum.SU2TorusRPLayoutMaster (a_pos)

variable {M : Nat} (hM : 1 ≤ M) (P C : List Z4Link) (hnd : (P ++ C ++ P.map (reflLink M)).Nodup)
  (hC : C.Nodup)
  (hCcov : ∀ ℓ : Z4Link, InBox (2 * M) ℓ.1 → linkSide M ℓ = .cross → ℓ ∈ C)
  (hPcov : ∀ ℓ : Z4Link, InBox (2 * M) ℓ.1 → linkSide M ℓ = .pos → ℓ ∈ P)
  (hPbox : ∀ x ∈ P, InBox (2 * M) x.1)

include hM hCcov hPcov in
theorem mem_lay (ℓ : Z4Link) (hb : InBox (2 * M) ℓ.1) : ℓ ∈ P ++ C ++ P.map (reflLink M) := by
  cases hs : linkSide M ℓ with
  | pos => exact List.mem_append_left _ (List.mem_append_left _ (hPcov ℓ hb hs))
  | cross => exact List.mem_append_left _ (List.mem_append_right _ (hCcov ℓ hb hs))
  | neg =>
    have hb' := YMGap.Continuum.SU2TorusRPMirGeom.refl_box hM ℓ hb
    have hp : linkSide M (reflLink M ℓ) = .pos := by rw [side_refl hM ℓ hb, hs]; rfl
    refine List.mem_append_right _ (List.mem_map.mpr ⟨reflLink M ℓ, hPcov _ hb' hp, refl_invol hM ℓ hb⟩)

include hM hCcov hPcov in
theorem hps_lay (p : Z4Plaq) (hp : InBox (2 * M) p.1) :
    ∀ b ∈ plaqIdx (P ++ C ++ P.map (reflLink M)) (2 * M) p,
      b < (P.length + C.length) + (P.length + C.length) - 1 + 1 := by
  rw [YMGap.Continuum.SU2TorusRPMirGeom.plaqIdx_eq]
  intro b hb
  obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hb
  have hm := mem_lay hM P C hCcov hPcov ℓ
    (YMGap.Continuum.SU2TorusRPLayoutFactor.plaqLinks_box (by omega) p hp ℓ hℓ)
  have h := YMGap.Continuum.SU2TorusRPLayout.idxOf_lt ℓ _ hm
  simp only [List.length_append, List.length_map] at h
  have : 0 < C.length ∨ C.length = 0 := Nat.eq_zero_or_pos _ |>.symm
  omega

include hM hnd hPcov hPbox in
theorem hWp_lay (β : Q') (K : Nat) (pos : List Z4Plaq)
    (hposP : ∀ p ∈ pos, InBox (2 * M) p.1 ∧ plaqSide M p = .pos) :
    Sup (P.length + C.length)
      (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (P ++ C ++ P.map (reflLink M)) (2 * M) β K) pos) := by
  refine YMGap.Continuum.SU2TorusRPSupTK.sup_prodTK _ _ β K pos fun p hp => ?_
  rw [YMGap.Continuum.SU2TorusRPMirGeom.plaqIdx_eq]
  intro b hb
  obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hb
  have hlb := YMGap.Continuum.SU2TorusRPLayoutFactor.plaqLinks_box (by omega) p (hposP p hp).1 ℓ hℓ
  have hP := hPcov ℓ hlb (plaq_pos hM p (hposP p hp).1 (hposP p hp).2 ℓ hℓ)
  exact (YMGap.Continuum.SU2TorusRPLayout.lay_pos P C (reflLink M) hnd ℓ hP
    (YMGap.Continuum.SU2TorusRPLayoutFactor.hinjP hM P hPbox ℓ hlb)).1

include hM hC hCcov hPcov hPbox in
/-- `torus_rp_layout` with the index bound and `hWp` discharged. -/
theorem torus_rp_layout' {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (ps pos cross : List Z4Plaq)
    (hperm : ps.Perm (pos ++ pos.map (mir M) ++ cross))
    (hposP : ∀ p ∈ pos, InBox (2 * M) p.1 ∧ plaqSide M p = .pos)
    (hcross : ∀ q ∈ cross, InBox (2 * M) q.1 ∧ plaqSide M q = .cross) (hCne : C ≠ [])
    (hpsbox : ∀ p ∈ ps, InBox (2 * M) p.1)
    (hb : 0 < (P.length + C.length) + (P.length + C.length) - 1)
    (F : RatPoly) (hF : Sup (P.length + C.length) F) (X : RatPoly)
    (hX : X = polyMul (signSelectedPolynomial (4 * ((P.length + C.length) + (P.length + C.length)))
      (conjSel (layT (P ++ C ++ P.map (reflLink M))))
      (reindexQuaternionPolynomial (halfSwap (P.length + C.length)) F)) F)
    (hXfix : PE ((P.length + C.length) + (P.length + C.length) - 1 + 1)
      (applySelectedTranslationSteps hb (layChain M P C hnd (a_pos P C hCne)) X) X)
    (hsup : YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks
      ((P.length + C.length) + (P.length + C.length) - 1 + 1)
      (polyMul X (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (P ++ C ++ P.map (reflLink M)) (2 * M) β K) ps))) :
    (0 : Q') ≤ quaternionHaar ((P.length + C.length) + (P.length + C.length))
      (polyMul X (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (P ++ C ++ P.map (reflLink M)) (2 * M) β K) ps)) :=
  YMGap.Continuum.SU2TorusRPLayoutMaster.torus_rp_layout hM P C hnd hC hCcov hPcov hPbox hβ K ps pos cross hperm hposP
    hcross hCne hb F hF (hWp_lay hM P C hnd hPcov hPbox β K pos hposP) X hX hXfix hsup
    (fun p hp => hps_lay hM P C hCcov hPcov p (hpsbox p hp))

end YMGap.Continuum.SU2TorusRPLayoutBounds

#print axioms YMGap.Continuum.SU2TorusRPLayoutBounds.mem_lay
#print axioms YMGap.Continuum.SU2TorusRPLayoutBounds.hps_lay
#print axioms YMGap.Continuum.SU2TorusRPLayoutBounds.hWp_lay
#print axioms YMGap.Continuum.SU2TorusRPLayoutBounds.torus_rp_layout'
