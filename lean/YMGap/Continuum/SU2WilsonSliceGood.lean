/-
# Transfer matrix (2e): the actual Wilson slices satisfy `Good`, so Z = ∫_U Π_t T_t

ADDITIVE.  **Labels:** STRONG COUPLING / Wilson `T_K` track, fixed `K`; also true for U(1), not gap
evidence.

The slice-`t` factor is `W_t = Π_{slicePS t} T_K · Π_{slicePT t} T_K`, and its private blocks are
`S_t = idxOf (sliceV t)` (the temporal links `V_t`).

* `tk_local`: a temporal link at time `t'` is not a link of any spatial plaquette, nor of any
  timelike plaquette based at a time `t ≠ t'`.  So `T_K(p)` has zero exponent on its block.
* `good_slices`: `Good` holds for the slice list over any duplicate-free list of times.
* `z_transfer`: `∫ Π_{p∈torus} T_K(p) ≈ ∫ Π_{t<N} T_t`, where `T_t = ∫dV_t W_t` is a polynomial
  kernel in the remaining (spatial) blocks.  That is, `Z = ∫_U Π_t T_t(U_t, U_{t+1})`.

Still OPEN (done in commit 33): Z as a periodic chain of time-shifted kernels (trace form), via the translation of one kernel.
-/

import YMGap.Continuum.SU2SliceIntegrate
import YMGap.Continuum.SU2SliceOrder
import YMGap.Continuum.SU2PlaqSupport

namespace YMGap.Continuum.SU2WilsonSliceGood

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2HaarDisjointSupport (FreeOff)
open YMGap.Continuum.SU2PlaqSupport
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.SU2TorusSlice
open YMGap.Continuum.SU2SliceIntegrate
open YMGap.Continuum.SU2SliceOrder (sliceProd torus_prod_slice)

local infix:50 " ≈ " => Q'.eqv

variable (links : List Z4Link) (N : Nat) (β : Q') (K : Nat)

local notation "F" => YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K

theorem chi_free {A : Nat → Bool} {x : RatPoly} (hc : FreeOff A false (YMGap.Continuum.SU2CharacterSquareIdentity.U x 1)) :
    ∀ k, FreeOff A false (YMGap.Continuum.SU2WilsonCharacterPower.chiPow x k)
  | 0 => free_one _ _
  | k + 1 => free_mul _ _ hc (chi_free hc k)

theorem wil_free {A : Nat → Bool} {x : RatPoly} (a : Nat → Q')
    (hp : ∀ k, FreeOff A false (YMGap.Continuum.SU2WilsonCharacterPower.chiPow x k)) :
    ∀ K', FreeOff A false (YMGap.Continuum.SU2WilsonCharacterPower.wilsonPoly x a K')
  | 0 => free_map _ _ _ (hp 0)
  | K' + 1 => free_add _ _ (wil_free a hp K') (free_map _ _ _ (hp _))

theorem tk_free (p : Z4Plaq) : FreeOff (idxB links N p) false (F p) := by
  have m := fun {i : Nat} (h : i < 4) => qfree_link links N p (List.getElem_mem (l := plaqLinks N p) (n := i) h)
  have hw : QFree (idxB links N p) false (YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.plaqWord links N p) :=
    qfree_mul _ _ (qfree_mul _ _ (m (by decide : 0 < 4)) (m (by decide : 1 < 4)))
      (qfree_mul _ _ (qfree_conj _ _ (m (by decide : 2 < 4))) (qfree_conj _ _ (m (by decide : 3 < 4))))
  exact wil_free _ (chi_free (free_char _ _ hw.1 0).2) K

theorem mem_of_idx {a : Z4Link} : ∀ l : List Z4Link, l.idxOf a < l.length → a ∈ l
  | [], h => absurd h (Nat.not_lt_zero _)
  | x :: l, h => by
    rw [List.idxOf_cons] at h
    cases hx : (x == a) with
    | true => exact (beq_iff_eq.mp hx) ▸ List.mem_cons_self
    | false =>
      rw [hx, cond_false] at h
      exact List.mem_cons_of_mem _ (mem_of_idx l (Nat.lt_of_succ_lt_succ h))

theorem range_nd : ∀ n : Nat, (List.range n).Nodup
  | 0 => by rw [List.range_zero]; exact List.nodup_nil
  | n + 1 => by
    rw [List.range_succ]
    refine List.nodup_append.mpr ⟨range_nd n, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
      fun a ha b hb e => ?_⟩
    rcases List.mem_cons.mp hb with rfl | h
    · exact Nat.lt_irrefl _ (e ▸ List.mem_range.mp ha)
    · exact List.not_mem_nil h

/-- A link of `links` that is not a link of `p` carries a zero block in `T_K(p)`. -/
theorem tk_local_of (p : Z4Plaq) (ℓ : Z4Link) (hℓ : ℓ ∈ links) (hn : ℓ ∉ plaqLinks N p) (blocks : Nat) :
    BlockLocal blocks (· ≠ links.idxOf ℓ) (F p) := by
  intro t ht b _ hb
  have e : b = links.idxOf ℓ := Decidable.byContradiction hb
  subst e
  cases hB : idxB links N p (links.idxOf ℓ) with
  | false => exact tk_free links N β K p t ht _ hB
  | true =>
    obtain ⟨ℓ', h', hd⟩ := List.any_eq_true.mp hB
    have hi : links.idxOf ℓ' = links.idxOf ℓ := of_decide_eq_true hd
    have hm : ℓ' ∈ links := mem_of_idx links (hi ▸ List.idxOf_lt_length_of_mem hℓ)
    exact absurd (idxOf_inj hm hℓ hi ▸ h') hn

/-- Temporal links of time `t'` avoid every plaquette of slice `t ≠ t'`, and every spatial plaquette. -/
theorem not_link (t t' : Nat) (ht : t ≠ t') (ℓ : Z4Link) (hs : linkSlice ℓ = (t', true)) (p : Z4Plaq)
    (hp : p ∈ slicePS N t ∨ p ∈ slicePT N t) : ℓ ∉ plaqLinks N p := fun hm => by
  rcases hp with hp | hp
  · have := plaq_slice_spatial N p ((mem_slicePS N t p).mp hp).2.2 ℓ hm
    rw [hs] at this; cases this
  · obtain ⟨_, ht0, hT⟩ := (mem_slicePT N t p).mp hp
    obtain ⟨v, P⟩ := p
    obtain ⟨_, _, hL, h1, h2, h3, h4⟩ := plaq_slice_time N v P hT
    rw [hL] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · rw [h1] at hs; exact ht (ht0 ▸ (Prod.mk.inj hs).1)
    · rw [h2] at hs; cases hs
    · rw [h3] at hs; exact ht (ht0 ▸ (Prod.mk.inj hs).1)
    · rw [h4] at hs; cases hs

/-- The slice factors with their private (temporal) blocks. -/
def wsl (ts : List Nat) : List (RatPoly × List Nat) :=
  ts.map fun t => (polyMul (prodPoly F (slicePS N t)) (prodPoly F (slicePT N t)), (sliceV N t).map links.idxOf)

theorem kprod_wsl : ∀ ts : List Nat, kprod (wsl links N β K ts) = sliceProd F N ts
  | [] => rfl
  | t :: ts => by
    show polyMul _ (kprod (wsl links N β K ts)) = _
    rw [kprod_wsl ts]; rfl

theorem local_of_all {blocks : Nat} {a : Nat → Prop} {X : RatPoly}
    (h : ∀ b, ¬ a b → BlockLocal blocks (· ≠ b) X) : BlockLocal blocks a X :=
  fun t ht b hb hn => h b hn t ht b hb (fun e => e rfl)

theorem prod_local {blocks : Nat} {a : Nat → Prop} (G : Z4Plaq → RatPoly) : ∀ ps : List Z4Plaq,
    (∀ p ∈ ps, BlockLocal blocks a (G p)) → BlockLocal blocks a (prodPoly G ps)
  | [], _ => BlockLocal.one _ _
  | p :: ps, h => BlockLocal.mul (h p List.mem_cons_self) (prod_local G ps fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem W_local (blocks t t' : Nat) (ht : t ≠ t') (ℓ : Z4Link) (hℓ : ℓ ∈ links) (hs : linkSlice ℓ = (t', true)) :
    BlockLocal blocks (· ≠ links.idxOf ℓ) (polyMul (prodPoly F (slicePS N t)) (prodPoly F (slicePT N t))) :=
  BlockLocal.mul
    (prod_local _ _ fun p hp => tk_local_of links N β K p ℓ hℓ (not_link N t t' ht ℓ hs p (Or.inl hp)) blocks)
    (prod_local _ _ fun p hp => tk_local_of links N β K p ℓ hℓ (not_link N t t' ht ℓ hs p (Or.inr hp)) blocks)

/-- **`Good` for the actual Wilson slices (PROVED).** -/
theorem good_slices (hL : ∀ ℓ ∈ torusLinks N, ℓ ∈ links) : ∀ ts : List Nat, ts.Nodup →
    Good links.length (wsl links N β K ts)
  | [], _ => trivial
  | t :: ts, hn => by
    obtain ⟨hnt, hn'⟩ := List.nodup_cons.mp hn
    refine ⟨fun b hb => ?_, local_of_all fun b hb => ?_, fun v hv => ?_, good_slices hL ts hn'⟩
    · obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hb
      exact List.idxOf_lt_length_of_mem (hL ℓ (List.mem_filter.mp hℓ).1)
    · have hm : b ∈ allS (wsl links N β K ts) := Decidable.byContradiction hb
      obtain ⟨w, hw, hbw⟩ := List.mem_flatMap.mp hm
      obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hw
      obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hbw
      exact W_local links N β K _ t t' (fun e => hnt (e ▸ ht')) ℓ (hL ℓ (List.mem_filter.mp hℓ).1)
        ((mem_sliceV N t' ℓ).mp hℓ).2
    · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hv
      refine local_of_all fun b hb => ?_
      have hm : b ∈ (sliceV N t).map links.idxOf := Decidable.byContradiction hb
      obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hm
      exact W_local links N β K _ t' t (fun e => hnt (e ▸ ht')) ℓ (hL ℓ (List.mem_filter.mp hℓ).1)
        ((mem_sliceV N t ℓ).mp hℓ).2

/-- **Z as an integral of slice kernels (PROVED).**  STRONG COUPLING / Wilson `T_K`, fixed `K`.
`∫ Π_{p∈torus} T_K(p) ≈ ∫ Π_{t<N} T_t` with `T_t = ∫dV_t W_t`. -/
theorem z_transfer (hL : ∀ ℓ ∈ torusLinks N, ℓ ∈ links) :
    quaternionHaar links.length (prodPoly F (torusPlaquettes N)) ≈
      quaternionHaar links.length (kprod (kint (wsl links N β K (List.range N)))) := by
  refine Q'.eqv_trans _ _ _ (SU2CharacterHaarBound.haar_coeff (torus_prod_slice F N) _) ?_
  rw [← kprod_wsl links N β K]
  exact slice_integrate _ _ (good_slices links N β K hL _ (range_nd N))

end YMGap.Continuum.SU2WilsonSliceGood
