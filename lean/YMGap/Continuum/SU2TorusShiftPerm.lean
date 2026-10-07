/-
# Torus RP (g1): the time shift `shv` permutes the whole torus (plaquettes and links)

* `shv_perm`: if membership in `l` is `InBox N x.1` and `l` is Nodup, then `l.map (shv N t) ~ l` (any `t`, `0 < N`).
* `tp_shift_perm`, `tl_shift_perm`: the instances for `torusPlaquettes N` and `torusLinks N`.

This is item 2 of the correlator split in `docs/J04-TORUS-RP-CS-SHAPE-2026-10-07.md`. It builds on the Prover's
`SU2TimeShift` (`shv`, `nodup_map_on`) without editing it. Items 1, 3, 4, 5 (`τ_t`, `Π T_K` invariance, Haar
invariance, `Θ∘τ = τ⁻¹∘Θ`) remain OPEN.
-/

import YMGap.Continuum.SU2TimeShift

namespace YMGap.Continuum.SU2TorusShiftPerm

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TimeShift (vs shv nodup_map_on)

theorem m2 (x N : Nat) (h : x < N + N) : x % N = if x < N then x else x - N := by
  split
  · exact Nat.mod_eq_of_lt (by assumption)
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem shift_eq (N t a : Nat) (hN : 0 < N) (ha : a < N) : (a + t) % N = if a + t % N < N then a + t % N else a + t % N - N := by
  have hr := Nat.mod_lt t hN
  rw [Nat.add_mod, Nat.mod_eq_of_lt ha]; exact m2 _ _ (by omega)

theorem shift_inj (N t a a' : Nat) (hN : 0 < N) (ha : a < N) (ha' : a' < N) (h : (a + t) % N = (a' + t) % N) : a = a' := by
  rw [shift_eq N t a hN ha, shift_eq N t a' hN ha'] at h
  have hr := Nat.mod_lt t hN
  split at h <;> split at h <;> omega

theorem shift_surj (N t a : Nat) (hN : 0 < N) (ha : a < N) :
    ((a + (N - t % N)) % N + t) % N = a ∧ (a + (N - t % N)) % N < N := by
  have hr := Nat.mod_lt t hN
  have hb := Nat.mod_lt (a + (N - t % N)) hN
  refine ⟨?_, hb⟩
  rw [shift_eq N t _ hN hb, m2 _ _ (by omega)]
  split <;> split <;> omega

theorem shv_perm {β : Type} [DecidableEq β] (N t : Nat) (hN : 0 < N) (l : List (Z4Vertex × β))
    (hmem : ∀ x, x ∈ l ↔ InBox N x.1) (hnd : l.Nodup) : (l.map (shv N t)).Perm l := by
  refine YMGap.Continuum.SU2TorusRPPermExt.perm_ext' _ _ (nodup_map_on _ _ ?_ hnd) hnd fun x => ?_
  · intro x hx y hy e
    obtain ⟨⟨a, b, c, d⟩, P⟩ := x
    obtain ⟨⟨a', b', c', d'⟩, P'⟩ := y
    have h1 := ((hmem _).mp hx).1
    have h2 := ((hmem _).mp hy).1
    simp only [shv, vs, Prod.mk.injEq] at e
    obtain ⟨⟨e1, e2, e3, e4⟩, e5⟩ := e
    have := shift_inj N t a a' hN h1 h2 e1
    subst this; subst e2; subst e3; subst e4; subst e5; rfl
  · obtain ⟨⟨a, b, c, d⟩, P⟩ := x
    constructor
    · intro hx
      obtain ⟨⟨⟨a', b', c', d'⟩, P'⟩, hy, e⟩ := List.mem_map.mp hx
      obtain ⟨h1, h2, h3, h4⟩ := (hmem _).mp hy
      simp only [shv, vs, Prod.mk.injEq] at e
      obtain ⟨⟨e1, e2, e3, e4⟩, e5⟩ := e
      subst e2; subst e3; subst e4; subst e5
      exact (hmem _).mpr ⟨e1 ▸ Nat.mod_lt _ hN, h2, h3, h4⟩
    · intro hx
      obtain ⟨h1, h2, h3, h4⟩ := (hmem _).mp hx
      obtain ⟨hs, hlt⟩ := shift_surj N t a hN h1
      refine List.mem_map.mpr ⟨(((a + (N - t % N)) % N, b, c, d), P), (hmem _).mpr ⟨hlt, h2, h3, h4⟩, ?_⟩
      simp only [shv, vs, hs]

theorem tp_shift_perm (N t : Nat) (hN : 0 < N) : ((torusPlaquettes N).map (shv N t)).Perm (torusPlaquettes N) :=
  shv_perm N t hN _ (fun x => mem_torusPlaquettes N x.1 x.2) (torusPlaquettes_nodup N)

theorem tl_shift_perm (N t : Nat) (hN : 0 < N) : ((torusLinks N).map (shv N t)).Perm (torusLinks N) :=
  shv_perm N t hN _ (fun x => mem_torusLinks N x.1 x.2) (torusLinks_nodup N)

end YMGap.Continuum.SU2TorusShiftPerm

#print axioms YMGap.Continuum.SU2TorusShiftPerm.tp_shift_perm
#print axioms YMGap.Continuum.SU2TorusShiftPerm.tl_shift_perm
