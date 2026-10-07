/-
# Torus RP (d9q): the concrete choice of `P` and `C` from the torus links

`Pt M = pos links of torusLinks (2M)`, `Ct M = crossing links of torusLinks (2M)`. Proved: the layout
`Pt ++ Ct ++ Θ Pt` is nodup, `Ct` is nodup and nonempty, `Ct ⊇` in-box crossing links, `Pt ⊇` in-box pos links, `Pt` in
the box — i.e. all link-side hypotheses of `torus_rp_layL`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPLayoutRPL

namespace YMGap.Continuum.SU2TorusRPChoosePC

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusRPGeom (reflLink linkSide Side refl_invol side_refl)

def Pt (M : Nat) : List Z4Link := (torusLinks (2 * M)).filter fun ℓ => linkSide M ℓ == .pos
def Ct (M : Nat) : List Z4Link := (torusLinks (2 * M)).filter fun ℓ => linkSide M ℓ == .cross

theorem mem_Pt {M : Nat} (ℓ : Z4Link) : ℓ ∈ Pt M ↔ InBox (2 * M) ℓ.1 ∧ linkSide M ℓ = .pos := by
  unfold Pt; rw [List.mem_filter, beq_iff_eq]
  exact and_congr_left' (mem_torusLinks _ ℓ.1 ℓ.2)

theorem mem_Ct {M : Nat} (ℓ : Z4Link) : ℓ ∈ Ct M ↔ InBox (2 * M) ℓ.1 ∧ linkSide M ℓ = .cross := by
  unfold Ct; rw [List.mem_filter, beq_iff_eq]
  exact and_congr_left' (mem_torusLinks _ ℓ.1 ℓ.2)

theorem nodup_map_on (f : Z4Link → Z4Link) : ∀ l : List Z4Link, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) →
    l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, h, hn => by
    rw [List.map_cons]
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_map_on f l
      (fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) (List.nodup_cons.mp hn).2⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.mp hm
    have := h b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self ..) e
    exact (List.nodup_cons.mp hn).1 (this ▸ hb)

variable {M : Nat} (hM : 1 ≤ M)

theorem Ct_nodup : (Ct M).Nodup := (torusLinks_nodup _).filter _

include hM in
theorem Ct_ne : Ct M ≠ [] := fun h => by
  have : (((0, 0, 0, 0), Dir4.x0) : Z4Link) ∈ Ct M :=
    (mem_Ct _).mpr ⟨⟨show 0 < 2 * M by omega, show 0 < 2 * M by omega, show 0 < 2 * M by omega,
      show 0 < 2 * M by omega⟩, rfl⟩
  rw [h] at this; exact List.not_mem_nil this

include hM in
theorem lay_nodup : (Pt M ++ Ct M ++ (Pt M).map (reflLink M)).Nodup := by
  have hP : (Pt M).Nodup := (torusLinks_nodup _).filter _
  have hmap : ((Pt M).map (reflLink M)).Nodup := by
    refine nodup_map_on _ _ (fun x hx y hy e => ?_) hP
    rw [← refl_invol hM x ((mem_Pt x).mp hx).1, e, refl_invol hM y ((mem_Pt y).mp hy).1]
  have hneg : ∀ z ∈ (Pt M).map (reflLink M), linkSide M z = .neg := fun z hz => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    rw [side_refl hM x ((mem_Pt x).mp hx).1, ((mem_Pt x).mp hx).2]; rfl
  refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hP, Ct_nodup, fun a ha b hb e => ?_⟩, hmap,
    fun a ha b hb e => ?_⟩
  · subst e; have h1 := ((mem_Pt a).mp ha).2; rw [((mem_Ct a).mp hb).2] at h1; cases h1
  · subst e
    have h2 := hneg a hb
    rcases List.mem_append.mp ha with ha | ha
    · rw [((mem_Pt a).mp ha).2] at h2; cases h2
    · rw [((mem_Ct a).mp ha).2] at h2; cases h2

open YMGap.Constructive in
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier in
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection in
include hM in
/-- `torus_rp_layL` with `P = Pt M`, `C = Ct M`: only the plaquette decomposition remains as hypothesis. -/
theorem torus_rp_PC {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (ps pos cross : List Z4Plaq)
    (hperm : ps.Perm (pos ++ pos.map (YMGap.Continuum.SU2TorusRPThetaProd.mir M) ++ cross))
    (hposP : ∀ p ∈ pos, InBox (2 * M) p.1 ∧ YMGap.Continuum.SU2TorusRPGeom.plaqSide M p = .pos)
    (hcross : ∀ q ∈ cross, InBox (2 * M) q.1 ∧ YMGap.Continuum.SU2TorusRPGeom.plaqSide M q = .cross)
    (hpsbox : ∀ p ∈ ps, InBox (2 * M) p.1)
    (F : RatPoly) (hF : YMGap.Continuum.SU2TorusRPCore.Sup (Pt M).length F) :
    (0 : Q') ≤ YMGap.Continuum.BF4GeometricHaarMehlerProjection.quaternionHaar
      ((Pt M).length + (Ct M).length + (Pt M).length)
      (polyMul (polyMul (signSelectedPolynomial (4 * (((Pt M).length + (Ct M).length) + ((Pt M).length + (Ct M).length)))
          (YMGap.Continuum.SU2TorusRPHaar.conjSel
            (YMGap.Continuum.SU2TorusRPLayoutT.layT (Pt M ++ Ct M ++ (Pt M).map (reflLink M))))
          (reindexQuaternionPolynomial (YMGap.Continuum.SU2TorusRPHalfSwap.halfSwap ((Pt M).length + (Ct M).length)) F)) F)
        (YMGap.Continuum.SU2HaarL1Activity.prodPoly
          (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (Pt M ++ Ct M ++ (Pt M).map (reflLink M)) (2 * M) β K) ps)) :=
  YMGap.Continuum.SU2TorusRPLayoutRPL.torus_rp_layL hM (Pt M) (Ct M) (lay_nodup hM) Ct_nodup (Ct_ne hM)
    (fun ℓ hb hs => (mem_Ct ℓ).mpr ⟨hb, hs⟩) (fun ℓ hb hs => (mem_Pt ℓ).mpr ⟨hb, hs⟩)
    (fun x hx => ((mem_Pt x).mp hx).1) hβ K ps pos cross hperm hposP hcross hpsbox F hF

end YMGap.Continuum.SU2TorusRPChoosePC

#print axioms YMGap.Continuum.SU2TorusRPChoosePC.lay_nodup
#print axioms YMGap.Continuum.SU2TorusRPChoosePC.Ct_ne
#print axioms YMGap.Continuum.SU2TorusRPChoosePC.mem_Pt
#print axioms YMGap.Continuum.SU2TorusRPChoosePC.torus_rp_PC
