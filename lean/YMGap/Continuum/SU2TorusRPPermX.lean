/-
# Torus RP (d9y): link-order permutations carrying an observable

`rcomp r` composes the reindexings of a list of block involutions, and `imap r` composes their block maps.
`perm_haarX`: for nodup `L₁ ~ L₂` (with `|L₁| = n`) containing every plaquette link, there is a list `r` with
`imap r (idx_{L₁} ℓ) = idx_{L₂} ℓ` for every link, and `∫ X·Π T_K[L₁] = ∫ (rcomp r X)·Π T_K[L₂]` for every supported
`X`. Matching the torus Θ with the layout Θ through `rcomp r` is not yet done.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPRelabelX
import YMGap.Continuum.SU2TorusRPSwap
import YMGap.Continuum.SU2ReindexPECongr

namespace YMGap.Continuum.SU2TorusRPPermX

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
  (QuaternionBlockInvolution reindexQuaternionPolynomial)
open YMGap.Continuum.SU2TorusRPCore (Sup)
open YMGap.Continuum.SU2TorusRPSwap (plaqL swapK swapInv swap_idx swap_plaqIdx plaqIdx_lt)

variable {n : Nat}

def rcomp : List (QuaternionBlockInvolution n) → RatPoly → RatPoly
  | [], X => X
  | σ :: r, X => reindexQuaternionPolynomial σ (rcomp r X)

def imap : List (QuaternionBlockInvolution n) → Nat → Nat
  | [], b => b
  | σ :: r, b => σ.map (imap r b)

theorem rcomp_append : ∀ (r₂ r₁ : List (QuaternionBlockInvolution n)) (X : RatPoly),
    rcomp (r₂ ++ r₁) X = rcomp r₂ (rcomp r₁ X)
  | [], _, _ => rfl
  | σ :: r₂, r₁, X => by
    show reindexQuaternionPolynomial σ (rcomp (r₂ ++ r₁) X) = _; rw [rcomp_append r₂ r₁ X]; rfl

theorem imap_append : ∀ (r₂ r₁ : List (QuaternionBlockInvolution n)) (b : Nat),
    imap (r₂ ++ r₁) b = imap r₂ (imap r₁ b)
  | [], _, _ => rfl
  | σ :: r₂, r₁, b => by
    show σ.map (imap (r₂ ++ r₁) b) = _; rw [imap_append r₂ r₁ b]; rfl

theorem rcomp_sup : ∀ (r : List (QuaternionBlockInvolution n)) (X : RatPoly), Sup n X → Sup n (rcomp r X)
  | [], _, h => h
  | σ :: _, _, _ => YMGap.Continuum.SU2ReindexPECongr.sup_reindex σ _

variable (N : Nat) (β : Q') (K : Nat) (ps : List Z4Plaq)

theorem perm_haarX_pre {A B : List Z4Link} (hAB : A.Perm B) : ∀ pre : List Z4Link, (pre ++ A).length = n →
    (pre ++ A).Nodup → (∀ p ∈ ps, ∀ ℓ ∈ plaqL N p, ℓ ∈ pre ++ A) →
    ∃ r : List (QuaternionBlockInvolution n), (∀ ℓ, imap r ((pre ++ A).idxOf ℓ) = (pre ++ B).idxOf ℓ) ∧
      ∀ X, Sup n X →
        (quaternionHaar n (polyMul X (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (pre ++ A) N β K) ps))).eqv
          (quaternionHaar n (polyMul (rcomp r X)
            (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (pre ++ B) N β K) ps))) := by
  induction hAB with
  | nil => intro pre _ _ _; exact ⟨[], fun _ => rfl, fun X _ => Q'.eqv_refl _⟩
  | cons x _ ih =>
    rename_i l₁ l₂ _
    intro pre hn hnd hmem
    rw [List.append_cons pre x l₁, List.append_cons pre x l₂]
    rw [List.append_cons pre x l₁] at hn hnd hmem
    exact ih _ hn hnd hmem
  | swap x y l =>
    intro pre hn hnd hmem
    have hp := (List.pairwise_append.1 hnd).2.1
    have hyx : y ≠ x := (List.pairwise_cons.1 hp).1 x (List.mem_cons_self ..)
    have hk : pre.length + 1 < n := by
      rw [← hn, List.length_append, List.length_cons, List.length_cons]; omega
    have hlt : ∀ p ∈ ps, ∀ b ∈ YMGap.Continuum.SU2TorusRPSplitTK.plaqIdx (pre ++ y :: x :: l) N p, b < n :=
      fun p hp' => hn ▸ plaqIdx_lt _ N p (hmem p hp')
    refine ⟨[swapInv n pre.length hk], fun ℓ => swap_idx pre l y x hyx ℓ, fun X hX => ?_⟩
    exact YMGap.Continuum.SU2TorusRPRelabelX.relabel_haarX _ _ N β K (swapInv n pre.length hk) ps hlt
      (fun p _ => swap_plaqIdx pre l y x hyx N p) X hX
  | trans h12 _ ih1 ih2 =>
    intro pre hn hnd hmem
    have hP := List.Perm.append_left pre h12
    obtain ⟨r₁, hi₁, h₁⟩ := ih1 pre hn hnd hmem
    obtain ⟨r₂, hi₂, h₂⟩ := ih2 pre (hP.length_eq ▸ hn) (hP.nodup_iff.1 hnd)
      fun p hp ℓ hℓ => hP.mem_iff.1 (hmem p hp ℓ hℓ)
    refine ⟨r₂ ++ r₁, fun ℓ => by rw [imap_append, hi₁, hi₂], fun X hX => ?_⟩
    rw [rcomp_append]
    exact Q'.eqv_trans _ _ _ (h₁ X hX) (h₂ _ (rcomp_sup r₁ X hX))

theorem perm_haarX {L₁ L₂ : List Z4Link} (h : L₁.Perm L₂) (hn : L₁.length = n) (hnd : L₁.Nodup)
    (hmem : ∀ p ∈ ps, ∀ ℓ ∈ plaqL N p, ℓ ∈ L₁) :
    ∃ r : List (QuaternionBlockInvolution n), (∀ ℓ, imap r (L₁.idxOf ℓ) = L₂.idxOf ℓ) ∧
      ∀ X, Sup n X →
        (quaternionHaar n (polyMul X (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK L₁ N β K) ps))).eqv
          (quaternionHaar n (polyMul (rcomp r X) (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK L₂ N β K) ps))) :=
  perm_haarX_pre N β K ps h [] hn hnd hmem

end YMGap.Continuum.SU2TorusRPPermX

#print axioms YMGap.Continuum.SU2TorusRPPermX.perm_haarX
