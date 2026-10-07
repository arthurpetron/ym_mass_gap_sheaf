/-
# Torus RP (d8c): the concrete split chain on the layout

For crossing links `C` in the layout `L = P ++ C ++ P.map Θ` (`a = |P| + |C| ≥ 1`), `layChain` has one direct
selected shear per `c ∈ C`: selected block `idx c`, multiplier `idx c + a` (a fresh block), side `left` at the cut
`t = 0` and `right` otherwise. `layChain_ok`: it is `ChainOK .direct` (distinct selected blocks, multipliers never
selected).

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPLayoutT

namespace YMGap.Continuum.SU2TorusRPLayoutChain

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2TorusRPSplitChain (ChainOK)
open YMGap.Continuum.SU2TorusRPGeom (reflLink)
open YMGap.Continuum.SU2TorusRPThetaPoly (getD_idxOf d0)

def sideOf (c : Z4Link) : SelectedTranslationSide := if c.1.1 = 0 then .left else .right

variable (M : Nat) (P C : List Z4Link)

/-- One split step for a crossing link. -/
def mkStep (ha : 1 ≤ P.length + C.length) (c : Z4Link) (hc : (P ++ C ++ P.map (reflLink M)).idxOf c < P.length + C.length) :
    SelectedTranslationStep (P.length + C.length + (P.length + C.length) - 1) where
  selected := (P ++ C ++ P.map (reflLink M)).idxOf c
  multiplier := (P ++ C ++ P.map (reflLink M)).idxOf c + (P.length + C.length)
  selected_lt := by omega
  multiplier_lt := by omega
  distinct := by omega
  side := sideOf c
  multiplierOrientation := .direct

/-- Chain over a sublist of crossing links (structural recursion, carrying the index bound). -/
def chainOf (ha : 1 ≤ P.length + C.length) :
    (L : List Z4Link) → (∀ c ∈ L, (P ++ C ++ P.map (reflLink M)).idxOf c < P.length + C.length) →
      List (SelectedTranslationStep (P.length + C.length + (P.length + C.length) - 1))
  | [], _ => []
  | c :: L, h => mkStep M P C ha c (h c (List.mem_cons_self ..)) ::
      chainOf ha L fun d hd => h d (List.mem_cons_of_mem _ hd)

def layChain (hnd : (P ++ C ++ P.map (reflLink M)).Nodup) (ha : 1 ≤ P.length + C.length) :
    List (SelectedTranslationStep (P.length + C.length + (P.length + C.length) - 1)) :=
  chainOf M P C ha C fun c hc => YMGap.Continuum.SU2TorusRPLayout.lay_cross P C (reflLink M) hnd c hc

theorem mem_chainOf (ha : 1 ≤ P.length + C.length) :
    ∀ (L : List Z4Link) (h : ∀ c ∈ L, (P ++ C ++ P.map (reflLink M)).idxOf c < P.length + C.length)
      (st : SelectedTranslationStep (P.length + C.length + (P.length + C.length) - 1)),
      st ∈ chainOf M P C ha L h →
      ∃ c ∈ L, st.selected = (P ++ C ++ P.map (reflLink M)).idxOf c ∧
        st.multiplier = (P ++ C ++ P.map (reflLink M)).idxOf c + (P.length + C.length) ∧
        st.multiplierOrientation = .direct ∧ st.side = sideOf c
  | [], _, _, hs => absurd hs List.not_mem_nil
  | c :: L, h, st, hs => by
      rcases List.mem_cons.mp hs with rfl | hm
      · exact ⟨c, List.mem_cons_self .., rfl, rfl, rfl, rfl⟩
      · obtain ⟨d, hd, e⟩ := mem_chainOf ha L _ st hm
        exact ⟨d, List.mem_cons_of_mem _ hd, e⟩

theorem chainOf_distinct (hnd : (P ++ C ++ P.map (reflLink M)).Nodup) (ha : 1 ≤ P.length + C.length) :
    ∀ (L : List Z4Link) (hL : ∀ c ∈ L, c ∈ C) (h : ∀ c ∈ L, (P ++ C ++ P.map (reflLink M)).idxOf c < P.length + C.length),
      L.Nodup → (chainOf M P C ha L h).Pairwise fun x y => x.selected ≠ y.selected
  | [], _, _, _ => List.Pairwise.nil
  | c :: L, hL, h, hnd' => by
      refine List.Pairwise.cons ?_ (chainOf_distinct hnd ha L (fun d hd => hL d (List.mem_cons_of_mem _ hd)) _
        (List.nodup_cons.mp hnd').2)
      intro st hst e
      obtain ⟨d, hd, hs, _⟩ := mem_chainOf M P C ha L _ st hst
      have hc := hL c (List.mem_cons_self ..)
      have hdC := hL d (List.mem_cons_of_mem _ hd)
      have hx := getD_idxOf (List.mem_append_left _ (List.mem_append_right P hc) : c ∈ P ++ C ++ P.map (reflLink M))
      have hy := getD_idxOf (List.mem_append_left _ (List.mem_append_right P hdC) : d ∈ P ++ C ++ P.map (reflLink M))
      have e' : (P ++ C ++ P.map (reflLink M)).idxOf c = (P ++ C ++ P.map (reflLink M)).idxOf d := by
        rw [← hs]; exact e
      apply (List.nodup_cons.mp hnd').1
      rw [show c = d by rw [← hx, ← hy, e']]; exact hd

theorem layChain_ok (hnd : (P ++ C ++ P.map (reflLink M)).Nodup) (ha : 1 ≤ P.length + C.length) (hC : C.Nodup) :
    ChainOK .direct (layChain M P C hnd ha) where
  orient st h := by obtain ⟨c, _, _, _, ho, _⟩ := mem_chainOf M P C ha C _ st h; exact ho
  distinct := chainOf_distinct M P C hnd ha C (fun _ h => h) _ hC
  fresh st h st' h' := by
    obtain ⟨c, hc, _, hm, _, _⟩ := mem_chainOf M P C ha C _ st h
    obtain ⟨c', hc', hs', _, _, _⟩ := mem_chainOf M P C ha C _ st' h'
    have := YMGap.Continuum.SU2TorusRPLayout.lay_cross P C (reflLink M) hnd c' hc'
    rw [hm, hs']; omega

end YMGap.Continuum.SU2TorusRPLayoutChain

#print axioms YMGap.Continuum.SU2TorusRPLayoutChain.layChain_ok
