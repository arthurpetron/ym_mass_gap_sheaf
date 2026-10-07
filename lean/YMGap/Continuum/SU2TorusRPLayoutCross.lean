/-
# Torus RP (d9a): crossing plaquettes on the layout are RPK after the split

On `L = P ++ C ++ P.map Θ` with the concrete chain `layChain`:
* `img_cross`: `img (idx c) = sideMul (sideOf c) U_{idx c + a} U_{idx c}` for `c ∈ C`;
* `img_pos`, `img_mir`: positive links and their mirrors are unchanged;
* `rpk_lay0`, `rpk_layM`: a crossing plaquette with index list `[idx c₁, idx ℓ, idx c₂, idx Θℓ]` (cut 0, `cᵢ` at time
  0) or `[idx c₁, idx Θℓ, idx c₂, idx ℓ]` (cut M, `cᵢ` not at time 0), `ℓ ∈ P` spatial, has an RPK `Ctw`-twist with
  the layout selector `layT`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPLayoutChain

namespace YMGap.Continuum.SU2TorusRPLayoutCross

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2TorusRPSplitChain (chImg sideMul multQ)
open YMGap.Continuum.SU2TorusRPSplitTK (plaqIdx imgTK)
open YMGap.Continuum.SU2TorusRPGeom (reflLink)
open YMGap.Continuum.SU2TorusRPThetaTK (isT)
open YMGap.Continuum.SU2TorusRPLayoutChain (sideOf mkStep chainOf layChain mem_chainOf)
open YMGap.Continuum.SU2TorusRPLayoutT (layT layT_fresh layT_link refl_dir)
open YMGap.Continuum.SU2TorusRPCore (RPK)
open YMGap.Continuum.SU2TorusRPCrossC (Ctw)
open PolyQuaternion (mul conj)

local notation "cv" => PolyQuaternion.coordinateVariable

variable (M : Nat) (P C : List Z4Link) (hnd : (P ++ C ++ P.map (reflLink M)).Nodup)
  (ha : 1 ≤ P.length + C.length)

include hnd in
theorem lay_cross_ge (c : Z4Link) (hc : c ∈ C) : P.length ≤ (P ++ C ++ P.map (reflLink M)).idxOf c := by
  have hd := List.nodup_append.mp hnd
  have hd2 := List.nodup_append.mp hd.1
  have hnP : c ∉ P := fun h => hd2.2.2 _ h _ hc rfl
  rw [YMGap.Continuum.SU2TorusRPLayout.idxOf_left c (P ++ C) _ (List.mem_append_right _ hc),
    YMGap.Continuum.SU2TorusRPHalfOrder.idxOf_append_nmem c P C hnP]
  exact Nat.le_add_right _ _

theorem mkStep_mem (c : Z4Link) :
    ∀ (L : List Z4Link) (h : ∀ c ∈ L, (P ++ C ++ P.map (reflLink M)).idxOf c < P.length + C.length) (hc : c ∈ L),
      ∃ st ∈ chainOf M P C ha L h, st.selected = (P ++ C ++ P.map (reflLink M)).idxOf c ∧
        st.multiplier = (P ++ C ++ P.map (reflLink M)).idxOf c + (P.length + C.length) ∧ st.side = sideOf c
  | [], _, hc => absurd hc List.not_mem_nil
  | d :: L, h, hc => by
      by_cases e : d = c
      · subst e; exact ⟨_, List.mem_cons_self .., rfl, rfl, rfl⟩
      · rcases List.mem_cons.mp hc with e' | hm
        · exact absurd e'.symm e
        · obtain ⟨st, hst, h1⟩ := mkStep_mem c L _ hm
          exact ⟨st, List.mem_cons_of_mem _ hst, h1⟩

include hnd in
theorem img_cross (hC : C.Nodup) (c : Z4Link) (hc : c ∈ C) :
    chImg .direct (layChain M P C hnd ha) ((P ++ C ++ P.map (reflLink M)).idxOf c) =
      sideMul (sideOf c) (cv ((P ++ C ++ P.map (reflLink M)).idxOf c + (P.length + C.length)))
        (cv ((P ++ C ++ P.map (reflLink M)).idxOf c)) := by
  obtain ⟨st, hst, hs, hm, hsd⟩ := mkStep_mem M P C ha c C _ hc
  have h := YMGap.Continuum.SU2TorusRPCrossMatch.chImg_sel .direct (layChain M P C hnd ha)
    (YMGap.Continuum.SU2TorusRPLayoutChain.layChain_ok M P C hnd ha hC).distinct st hst
  rw [hs] at h; rw [h, hsd, hm]; rfl

include hnd in
theorem img_other (b : Nat) (hb : ∀ c ∈ C, b ≠ (P ++ C ++ P.map (reflLink M)).idxOf c) :
    chImg .direct (layChain M P C hnd ha) b = cv b :=
  YMGap.Continuum.SU2TorusRPCrossMatch.chImg_unsel .direct b _ fun st hst => by
    obtain ⟨c, hc, hs, _⟩ := mem_chainOf M P C ha C _ st hst
    rw [hs]; exact hb c hc

include hnd in
theorem img_pos (ℓ : Z4Link) (hℓ : ℓ ∈ P) :
    chImg .direct (layChain M P C hnd ha) ((P ++ C ++ P.map (reflLink M)).idxOf ℓ) =
      cv ((P ++ C ++ P.map (reflLink M)).idxOf ℓ) := by
  refine img_other M P C hnd ha _ fun c hc e => ?_
  have h1 := lay_cross_ge M P C hnd c hc
  rw [YMGap.Continuum.SU2TorusRPLayout.idxOf_left ℓ (P ++ C) _ (List.mem_append_left _ hℓ),
    YMGap.Continuum.SU2TorusRPLayout.idxOf_left ℓ P C hℓ] at e
  have := YMGap.Continuum.SU2TorusRPLayout.idxOf_lt ℓ P hℓ
  omega

include hnd in
theorem img_hi (b : Nat) (hb : P.length + C.length ≤ b) : chImg .direct (layChain M P C hnd ha) b = cv b := by
  refine img_other M P C hnd ha _ fun c hc e => ?_
  have := YMGap.Continuum.SU2TorusRPLayout.lay_cross P C (reflLink M) hnd c hc
  omega

theorem layT_hi (c : Z4Link) (hc : c ∈ C) (hnd' : (P ++ C ++ P.map (reflLink M)).Nodup) :
    layT (P ++ C ++ P.map (reflLink M)) ((P ++ C ++ P.map (reflLink M)).idxOf c + (P.length + C.length)) = true := by
  refine layT_fresh _ _ ?_
  have := lay_cross_ge M P C hnd' c hc
  simp only [List.length_append, List.length_map]; omega

theorem rpk_lay0 {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (hC : C.Nodup) (q : Z4Plaq)
    (c1 c2 ℓ : Z4Link) (h1 : c1 ∈ C) (h2 : c2 ∈ C) (hℓ : ℓ ∈ P) (hs : isT ℓ.2 = false)
    (hinj : ∀ x ∈ P, reflLink M x = reflLink M ℓ → x = ℓ)
    (hside1 : c1.1.1 = 0) (hside2 : c2.1.1 = 0)
    (hidx : plaqIdx (P ++ C ++ P.map (reflLink M)) (2 * M) q =
      [(P ++ C ++ P.map (reflLink M)).idxOf c1, (P ++ C ++ P.map (reflLink M)).idxOf ℓ,
       (P ++ C ++ P.map (reflLink M)).idxOf c2, (P ++ C ++ P.map (reflLink M)).idxOf (reflLink M ℓ)]) :
    RPK (P.length + C.length) (Ctw (P.length + C.length) (layT (P ++ C ++ P.map (reflLink M)))
      (imgTK (P ++ C ++ P.map (reflLink M)) (2 * M) β K (chImg .direct (layChain M P C hnd ha)) q)) := by
  obtain ⟨hp, hpa⟩ := YMGap.Continuum.SU2TorusRPLayout.lay_pos P C (reflLink M) hnd ℓ hℓ hinj
  rw [hpa] at hidx
  refine YMGap.Continuum.SU2TorusRPCrossMatch.rpk_match0 hβ K _ _ _ _ q _ _ _ hidx
    (YMGap.Continuum.SU2TorusRPLayout.lay_cross P C (reflLink M) hnd c1 h1) hp
    (YMGap.Continuum.SU2TorusRPLayout.lay_cross P C (reflLink M) hnd c2 h2) ?_ (img_pos M P C hnd ha ℓ hℓ) ?_
    (img_hi M P C hnd ha _ (Nat.le_add_left _ _)) (layT_hi M P C c1 h1 hnd) (layT_hi M P C c2 h2 hnd) ?_
  · rw [img_cross M P C hnd ha hC c1 h1]; unfold sideOf; rw [if_pos hside1]; rfl
  · rw [img_cross M P C hnd ha hC c2 h2]; unfold sideOf; rw [if_pos hside2]; rfl
  · rw [← hpa, layT_link _ _ (List.mem_append_right _ (List.mem_map_of_mem hℓ)), refl_dir, hs]

theorem rpk_layM {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (hC : C.Nodup) (q : Z4Plaq)
    (c1 c2 ℓ : Z4Link) (h1 : c1 ∈ C) (h2 : c2 ∈ C) (hℓ : ℓ ∈ P) (hs : isT ℓ.2 = false)
    (hinj : ∀ x ∈ P, reflLink M x = reflLink M ℓ → x = ℓ)
    (hside1 : c1.1.1 ≠ 0) (hside2 : c2.1.1 ≠ 0)
    (hidx : plaqIdx (P ++ C ++ P.map (reflLink M)) (2 * M) q =
      [(P ++ C ++ P.map (reflLink M)).idxOf c1, (P ++ C ++ P.map (reflLink M)).idxOf (reflLink M ℓ),
       (P ++ C ++ P.map (reflLink M)).idxOf c2, (P ++ C ++ P.map (reflLink M)).idxOf ℓ]) :
    RPK (P.length + C.length) (Ctw (P.length + C.length) (layT (P ++ C ++ P.map (reflLink M)))
      (imgTK (P ++ C ++ P.map (reflLink M)) (2 * M) β K (chImg .direct (layChain M P C hnd ha)) q)) := by
  obtain ⟨hp, hpa⟩ := YMGap.Continuum.SU2TorusRPLayout.lay_pos P C (reflLink M) hnd ℓ hℓ hinj
  rw [hpa] at hidx
  refine YMGap.Continuum.SU2TorusRPCrossMatch.rpk_matchM hβ K _ _ _ _ q _ _ _ hidx
    (YMGap.Continuum.SU2TorusRPLayout.lay_cross P C (reflLink M) hnd c1 h1) hp
    (YMGap.Continuum.SU2TorusRPLayout.lay_cross P C (reflLink M) hnd c2 h2) ?_ (img_pos M P C hnd ha ℓ hℓ) ?_
    (img_hi M P C hnd ha _ (Nat.le_add_left _ _)) (layT_hi M P C c1 h1 hnd) (layT_hi M P C c2 h2 hnd) ?_
  · rw [img_cross M P C hnd ha hC c1 h1]; unfold sideOf; rw [if_neg hside1]; rfl
  · rw [img_cross M P C hnd ha hC c2 h2]; unfold sideOf; rw [if_neg hside2]; rfl
  · rw [← hpa, layT_link _ _ (List.mem_append_right _ (List.mem_map_of_mem hℓ)), refl_dir, hs]

end YMGap.Continuum.SU2TorusRPLayoutCross

#print axioms YMGap.Continuum.SU2TorusRPLayoutCross.rpk_lay0
#print axioms YMGap.Continuum.SU2TorusRPLayoutCross.rpk_layM
