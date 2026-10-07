/-
# Torus RP (d6b): evaluating the split image on plaquettes

* `chImg_sel`, `chImg_unsel`: the chain image on selected / unselected blocks.
* `imgTK_eq_TK`: a plaquette none of whose links is split keeps its `T_K`.
* `rpk_match0`, `rpk_matchM`: a crossing plaquette whose four link indices are `[s₁, p, s₂, p + a]` (cut 0, left
  split) or `[s₁, p + a, s₂, p]` (cut M, right split), with multipliers `sᵢ + a`, has an RPK `Ctw`-twist.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPPELift

namespace YMGap.Continuum.SU2TorusRPCrossMatch

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2TorusRPSplitChain (chImg sideMul multQ)
open YMGap.Continuum.SU2TorusRPSplitTK (plaqIdx imgTK imgWord)
open YMGap.Continuum.SU2TorusRPCore (RPK)
open YMGap.Continuum.SU2TorusRPCrossC (Ctw)
open PolyQuaternion (mul conj)

local notation "cv" => PolyQuaternion.coordinateVariable

variable {tailBlocks : Nat}

theorem chImg_unsel (o : SelectedMultiplierOrientation) (b : Nat) :
    ∀ steps : List (SelectedTranslationStep tailBlocks), (∀ st ∈ steps, b ≠ st.selected) → chImg o steps b = cv b
  | [], _ => rfl
  | st :: r, h => by
      unfold chImg; rw [if_neg (h st (List.mem_cons_self ..))]
      exact chImg_unsel o b r fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem chImg_sel (o : SelectedMultiplierOrientation) :
    ∀ steps : List (SelectedTranslationStep tailBlocks), steps.Pairwise (fun x y => x.selected ≠ y.selected) →
      ∀ st ∈ steps, chImg o steps st.selected = sideMul st.side (multQ o st.multiplier) (cv st.selected)
  | [], _, st, h => absurd h List.not_mem_nil
  | x :: r, hp, st, h => by
      unfold chImg
      rcases List.mem_cons.mp h with rfl | hm
      · rw [if_pos rfl]
      · have hne : st.selected ≠ x.selected := fun e => (List.pairwise_cons.mp hp).1 st hm e.symm
        rw [if_neg hne]
        exact chImg_sel o r (List.pairwise_cons.mp hp).2 st hm

theorem imgTK_eq_TK (links : List Z4Link) (N : Nat) (β : Q') (K : Nat) (img : Nat → PolyQuaternion) (q : Z4Plaq)
    (h : ∀ b ∈ plaqIdx links N q, img b = cv b) :
    imgTK links N β K img q = YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K q := by
  unfold imgTK imgWord YMGap.Continuum.SU2WilsonPolymerIdentity.TK YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.plaqWord
    YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.linkVar
  rw [h _ (List.mem_cons_self ..), h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
    h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
    h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))]

theorem rpk_match0 {a : Nat} {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (T : Nat → Bool)
    (links : List Z4Link) (N : Nat) (img : Nat → PolyQuaternion) (q : Z4Plaq) (s1 p s2 : Nat)
    (hidx : plaqIdx links N q = [s1, p, s2, p + a])
    (h1 : s1 < a) (hp : p < a) (h2 : s2 < a)
    (hi1 : img s1 = mul (cv (s1 + a)) (cv s1)) (hip : img p = cv p) (hi2 : img s2 = mul (cv (s2 + a)) (cv s2))
    (hip' : img (p + a) = cv (p + a))
    (hT1 : T (s1 + a) = true) (hT2 : T (s2 + a) = true) (hTp : T (p + a) = false) :
    RPK a (Ctw a T (imgTK links N β K img q)) := by
  unfold plaqIdx at hidx
  simp only [List.cons.injEq, and_true] at hidx
  obtain ⟨e1, e2, e3, e4⟩ := hidx
  unfold imgTK imgWord
  rw [e1, e2, e3, e4, hi1, hip, hi2, hip']
  exact YMGap.Continuum.SU2TorusRPCrossC.rpk_C_cross0 K T hβ s1 p s2 h1 hp h2 hT1 hT2 hTp

theorem rpk_matchM {a : Nat} {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (T : Nat → Bool)
    (links : List Z4Link) (N : Nat) (img : Nat → PolyQuaternion) (q : Z4Plaq) (s1 p s2 : Nat)
    (hidx : plaqIdx links N q = [s1, p + a, s2, p])
    (h1 : s1 < a) (hp : p < a) (h2 : s2 < a)
    (hi1 : img s1 = mul (cv s1) (cv (s1 + a))) (hip : img p = cv p) (hi2 : img s2 = mul (cv s2) (cv (s2 + a)))
    (hip' : img (p + a) = cv (p + a))
    (hT1 : T (s1 + a) = true) (hT2 : T (s2 + a) = true) (hTp : T (p + a) = false) :
    RPK a (Ctw a T (imgTK links N β K img q)) := by
  unfold plaqIdx at hidx
  simp only [List.cons.injEq, and_true] at hidx
  obtain ⟨e1, e2, e3, e4⟩ := hidx
  unfold imgTK imgWord
  rw [e1, e2, e3, e4, hi1, hip, hi2, hip']
  exact YMGap.Continuum.SU2TorusRPCrossC.rpk_C_crossM K T hβ s1 p s2 h1 hp h2 hT1 hT2 hTp

end YMGap.Continuum.SU2TorusRPCrossMatch

#print axioms YMGap.Continuum.SU2TorusRPCrossMatch.chImg_sel
#print axioms YMGap.Continuum.SU2TorusRPCrossMatch.imgTK_eq_TK
#print axioms YMGap.Continuum.SU2TorusRPCrossMatch.rpk_match0
#print axioms YMGap.Continuum.SU2TorusRPCrossMatch.rpk_matchM
