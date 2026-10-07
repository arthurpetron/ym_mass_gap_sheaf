/-
# Torus RP (d9t): the torus plaquette decomposition; RP on the layout for all torus plaquettes

* `posT M`, `crossT M`: pos / crossing filters of `torusPlaquettes (2M)`.
* `plaq_perm`: `torusPlaquettes (2M) ~ posT ++ mir posT ++ crossT`.
* `torus_rp_all`: `0 ≤ ∫_{|L|} (Θ_H F · F) · ∏_{all torus plaquettes} T_K` on the layout
  `Pt ++ Ct ++ Θ Pt`, for every `F` on the first `|Pt|` blocks. No geometric hypotheses remain.

Open: identify this layout integral with the actual torus integrand (link order `torusLinks`, observables
placed on positive links) via block reindexing; then hW.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPChoosePC
import YMGap.Continuum.SU2TorusRPPermExt
import YMGap.Continuum.SU2TorusRPMirInv

namespace YMGap.Continuum.SU2TorusRPPlaqSplit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusRPGeom (reflLink plaqSide Side)
open YMGap.Continuum.SU2TorusRPThetaProd (mir)
open YMGap.Continuum.SU2TorusRPChoosePC (Pt Ct)

def posT (M : Nat) : List Z4Plaq := (torusPlaquettes (2 * M)).filter fun p => plaqSide M p == .pos
def crossT (M : Nat) : List Z4Plaq := (torusPlaquettes (2 * M)).filter fun p => plaqSide M p == .cross

theorem mem_tp {M : Nat} (p : Z4Plaq) : p ∈ torusPlaquettes (2 * M) ↔ InBox (2 * M) p.1 :=
  mem_torusPlaquettes _ p.1 p.2

theorem mem_posT {M : Nat} (p : Z4Plaq) : p ∈ posT M ↔ InBox (2 * M) p.1 ∧ plaqSide M p = .pos := by
  unfold posT; rw [List.mem_filter, beq_iff_eq, mem_tp]

theorem mem_crossT {M : Nat} (p : Z4Plaq) : p ∈ crossT M ↔ InBox (2 * M) p.1 ∧ plaqSide M p = .cross := by
  unfold crossT; rw [List.mem_filter, beq_iff_eq, mem_tp]

theorem nodup_map_on (f : Z4Plaq → Z4Plaq) : ∀ l : List Z4Plaq, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) →
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
include hM

theorem plaq_perm : (torusPlaquettes (2 * M)).Perm (posT M ++ (posT M).map (mir M) ++ crossT M) := by
  have hmirS : ∀ q ∈ (posT M).map (mir M), InBox (2 * M) q.1 ∧ plaqSide M q = .neg := fun q hq => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact YMGap.Continuum.SU2TorusRPMirGeom.mir_side hM p ((mem_posT p).mp hp).1 ((mem_posT p).mp hp).2
  refine YMGap.Continuum.SU2TorusRPPermExt.perm_ext' _ _ (torusPlaquettes_nodup _) ?_ (fun p => ?_)
  · have hP : (posT M).Nodup := (torusPlaquettes_nodup _).filter _
    have hC : (crossT M).Nodup := (torusPlaquettes_nodup _).filter _
    have hm : ((posT M).map (mir M)).Nodup := by
      refine nodup_map_on _ _ (fun x hx y hy e => ?_) hP
      rw [← YMGap.Continuum.SU2TorusRPMirInv.mir_invol hM x ((mem_posT x).mp hx).1, e,
        YMGap.Continuum.SU2TorusRPMirInv.mir_invol hM y ((mem_posT y).mp hy).1]
    refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hP, hm, fun a ha b hb e => ?_⟩, hC,
      fun a ha b hb e => ?_⟩
    · subst e; have h1 := ((mem_posT a).mp ha).2; rw [(hmirS a hb).2] at h1; cases h1
    · subst e
      have h2 := ((mem_crossT a).mp hb).2
      rcases List.mem_append.mp ha with ha | ha
      · rw [((mem_posT a).mp ha).2] at h2; cases h2
      · rw [(hmirS a ha).2] at h2; cases h2
  · rw [mem_tp]
    constructor
    · intro hb
      cases hs : plaqSide M p with
      | pos => exact List.mem_append_left _ (List.mem_append_left _ ((mem_posT p).mpr ⟨hb, hs⟩))
      | cross => exact List.mem_append_right _ ((mem_crossT p).mpr ⟨hb, hs⟩)
      | neg =>
        obtain ⟨hb', hs'⟩ := YMGap.Continuum.SU2TorusRPMirInv.mir_side_neg hM p hb hs
        refine List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨mir M p,
          (mem_posT _).mpr ⟨hb', hs'⟩, YMGap.Continuum.SU2TorusRPMirInv.mir_invol hM p hb⟩))
    · intro hp
      rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_append.mp hp with hp | hp
        · exact ((mem_posT p).mp hp).1
        · exact (hmirS p hp).1
      · exact ((mem_crossT p).mp hp).1

/-- Layout RP for the full torus plaquette product: no geometric hypotheses remain. -/
theorem torus_rp_all {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat)
    (F : RatPoly) (hF : YMGap.Continuum.SU2TorusRPCore.Sup (Pt M).length F) :
    (0 : Q') ≤ YMGap.Continuum.BF4GeometricHaarMehlerProjection.quaternionHaar
      ((Pt M).length + (Ct M).length + (Pt M).length)
      (polyMul (polyMul (signSelectedPolynomial (4 * (((Pt M).length + (Ct M).length) + ((Pt M).length + (Ct M).length)))
          (YMGap.Continuum.SU2TorusRPHaar.conjSel
            (YMGap.Continuum.SU2TorusRPLayoutT.layT (Pt M ++ Ct M ++ (Pt M).map (reflLink M))))
          (reindexQuaternionPolynomial (YMGap.Continuum.SU2TorusRPHalfSwap.halfSwap ((Pt M).length + (Ct M).length)) F)) F)
        (YMGap.Continuum.SU2HaarL1Activity.prodPoly
          (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (Pt M ++ Ct M ++ (Pt M).map (reflLink M)) (2 * M) β K)
          (torusPlaquettes (2 * M)))) :=
  YMGap.Continuum.SU2TorusRPChoosePC.torus_rp_PC hM hβ K _ (posT M) (crossT M) (plaq_perm hM)
    (fun p hp => (mem_posT p).mp hp) (fun q hq => (mem_crossT q).mp hq) (fun p hp => (mem_tp p).mp hp) F hF

end YMGap.Continuum.SU2TorusRPPlaqSplit

#print axioms YMGap.Continuum.SU2TorusRPPlaqSplit.plaq_perm
#print axioms YMGap.Continuum.SU2TorusRPPlaqSplit.torus_rp_all
