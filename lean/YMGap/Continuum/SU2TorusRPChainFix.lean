/-
# Torus RP (d9m): the split chain fixes `X = Θ_H F · F` (`hXfix`)

* `fix_list`: a nonempty admissible chain whose coordinate images are trivial off a set `bad` of blocks fixes every
  polynomial whose variables avoid `bad` (from `poly_fix`, `chain_coord`).
* `lay_fix`: on the layout, if `F` lives on the first `|P|` blocks, the concrete chain fixes `X = Θ_H F · F`: `F` uses
  blocks `< |P| ≤` crossing indices, and `Θ_H F` uses blocks `≥ a >` crossing indices.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPFixSub
import YMGap.Continuum.SU2TorusRPLayoutSup

namespace YMGap.Continuum.SU2TorusRPChainFix

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2HaarAlgebra (PE)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2TorusRPSplitChain (chImg ChainOK)
open YMGap.Continuum.SU2TorusRPCore (Sup)
open YMGap.Continuum.SU2TorusRPHaar (conjSel)
open YMGap.Continuum.SU2TorusRPGeom (reflLink)
open YMGap.Continuum.SU2TorusRPLayoutChain (layChain)
open YMGap.Continuum.SU2TorusRPLayoutT (layT)
open YMGap.Continuum.SU2TorusRPHalfSwap (halfSwap)

local notation "cv" => PolyQuaternion.coordinateVariable

theorem fix_list {T : Nat} (hb : 0 < T) (l : List (SelectedTranslationStep T)) (hne : l ≠ [])
    (hch : ChainOK .direct l) (bad : Nat → Prop) (hcv : ∀ b, b < T + 1 → ¬ bad b → chImg .direct l b = cv b)
    (X : RatPoly) (hX : ∀ t ∈ X, ∀ i, exponentAt t.1 i ≠ 0 → i < 4 * (T + 1) ∧ ¬ bad (i / 4)) :
    PE (T + 1) (applySelectedTranslationSteps hb l X) X := by
  cases l with
  | nil => exact absurd rfl hne
  | cons st r =>
    refine YMGap.Continuum.SU2TorusRPFixSub.poly_fix (YMGap.Continuum.SU2TorusRPStepSub.steps_ringSub hb _)
      (fun i => i < 4 * (T + 1) ∧ ¬ bad (i / 4)) ?_
      (fun p q => YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.applySelectedTranslationSteps_add hb _ p q)
      (fun p q h => YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates.applySelectedTranslationSteps_prefix hb _ h)
      (fun p => YMGap.Continuum.SU2TorusRPSplitChain.steps_supported_ne hb st r p) X hX
    intro i hi
    have hq := YMGap.Continuum.SU2TorusRPSplitChain.chain_coord .direct hb st r hch (i / 4) (by omega)
    rw [hcv _ (by omega) hi.2] at hq
    have key : ∀ c, c < 4 → PE (T + 1) (applySelectedTranslationSteps hb (st :: r) (polyVar (4 * (i / 4) + c)))
        (polyVar (4 * (i / 4) + c)) := fun c hc =>
      match c, hc with
      | 0, _ => hq.s
      | 1, _ => hq.i
      | 2, _ => hq.j
      | 3, _ => hq.k
    rw [show i = 4 * (i / 4) + i % 4 by omega]
    exact key _ (Nat.mod_lt _ (by decide))

theorem exp_ne_lt {m : List Nat} {i : Nat} (h : exponentAt m i ≠ 0) : i < m.length := by
  apply Nat.lt_of_not_le; intro hl
  exact h (YMGap.Continuum.SU2MultiLinkHaarFactorization.exponentAt_of_length_le m i hl)

variable (M : Nat) (P C : List Z4Link) (hnd : (P ++ C ++ P.map (reflLink M)).Nodup)
  (ha : 1 ≤ P.length + C.length)

include hnd in
theorem lay_fix (hC : C.Nodup) (hCne : C ≠ []) (hb : 0 < (P.length + C.length) + (P.length + C.length) - 1)
    (F : RatPoly) (hF : Sup P.length F) :
    PE ((P.length + C.length) + (P.length + C.length) - 1 + 1)
      (applySelectedTranslationSteps hb (layChain M P C hnd ha)
        (polyMul (signSelectedPolynomial (4 * ((P.length + C.length) + (P.length + C.length)))
          (conjSel (layT (P ++ C ++ P.map (reflLink M))))
          (reindexQuaternionPolynomial (halfSwap (P.length + C.length)) F)) F))
      (polyMul (signSelectedPolynomial (4 * ((P.length + C.length) + (P.length + C.length)))
          (conjSel (layT (P ++ C ++ P.map (reflLink M))))
          (reindexQuaternionPolynomial (halfSwap (P.length + C.length)) F)) F) := by
  have hne : layChain M P C hnd ha ≠ [] := by
    cases C with
    | nil => exact absurd rfl hCne
    | cons c C => intro h; cases h
  refine fix_list hb _ hne (YMGap.Continuum.SU2TorusRPLayoutChain.layChain_ok M P C hnd ha hC)
    (fun b => ∃ c ∈ C, b = (P ++ C ++ P.map (reflLink M)).idxOf c)
    (fun b _ hb' => YMGap.Continuum.SU2TorusRPLayoutCross.img_other M P C hnd ha b fun c hc e => hb' ⟨c, hc, e⟩)
    _ ?_
  intro t ht i hi
  simp only [polyMul, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨s, hs, u, hu, rfl⟩ := ht
  rw [YMGap.Continuum.SU2TorusRPFixPoly.emm] at hi
  rcases Nat.eq_zero_or_pos (exponentAt s.1 i) with hsi | hsi
  · -- the variable comes from `F`
    rw [hsi, Nat.zero_add] at hi
    have hl := Nat.lt_of_lt_of_le (exp_ne_lt hi) (hF u hu)
    refine ⟨by omega, fun ⟨c, hc, e⟩ => ?_⟩
    have := YMGap.Continuum.SU2TorusRPLayoutCross.lay_cross_ge M P C hnd c hc
    have hq : i / 4 < P.length :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mpr (by rw [Nat.mul_comm]; exact hl)
    exact absurd this (Nat.not_le.mpr (e ▸ hq))
  · -- the variable comes from `Θ_H F`
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    have hsi' : exponentAt (reindexQuaternionExponents (halfSwap (P.length + C.length)) w.1) i ≠ 0 :=
      Nat.pos_iff_ne_zero.mp hsi
    have hil := exp_ne_lt hsi'
    rw [reindexQuaternionExponents_length] at hil
    rw [exponentAt_reindexQuaternionExponents _ _ hil] at hsi'
    have hwl := Nat.lt_of_lt_of_le (exp_ne_lt hsi') (hF w hw)
    have hmap : (halfSwap (P.length + C.length)).map (i / 4) =
        YMGap.Continuum.SU2TorusRPHalfSwap.hsMap (P.length + C.length) (i / 4) := rfl
    rw [hmap] at hwl
    unfold YMGap.Continuum.SU2TorusRPHalfSwap.hsMap at hwl
    refine ⟨by omega, fun ⟨c, hc, e⟩ => ?_⟩
    have := YMGap.Continuum.SU2TorusRPLayout.lay_cross P C (reflLink M) hnd c hc
    rcases Nat.lt_or_ge (i / 4) (P.length + C.length) with h | h
    · rw [if_pos h] at hwl
      have h1 : 4 * (i / 4 + (P.length + C.length)) < 4 * P.length :=
        Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hwl
      have h2 : 4 * P.length ≤ 4 * (i / 4 + (P.length + C.length)) :=
        Nat.mul_le_mul_left 4 (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_left _ _))
      exact absurd h1 (Nat.not_lt.mpr h2)
    · rw [← e] at this
      exact absurd h (Nat.not_le.mpr this)

end YMGap.Continuum.SU2TorusRPChainFix

#print axioms YMGap.Continuum.SU2TorusRPChainFix.fix_list
#print axioms YMGap.Continuum.SU2TorusRPChainFix.lay_fix
#print axioms YMGap.Continuum.SU2TorusRPChainFix.exp_ne_lt
