/-
# Periodic time translation of the actual full torus lists

The literal `SU2TimeShift.shv N t` has the explicit inverse time shift
`N - t % N` on in-range vertices. It therefore permutes the SAME complete
torus link list. The inverse-list index identity supplies the link-coordinate
join consumed by `SU2TorusRPPermX.perm_haarX` and `SU2TimeShift.tk_shift`.

The full plaquette list, including temporal plaquettes, is also permuted.
These are finite geometric identities for every positive side and every
natural shift. OWN-mean translation and the RP/time pairing are consumers;
no analytic estimate or continuum conclusion is supplied here.
-/

import YMGap.Continuum.SU2TimeShift
import YMGap.Continuum.SU2TorusRPLayout

namespace YMGap.Continuum.SU2TorusLinksTimeShift

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress (Z4Vertex Z4Link Z4Plaq)
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TimeShift (vs shv)
open YMGap.Continuum.TorusWilsonAction
  (cancel_mod perm_of_nodup_mem shiftPlaq torusPlaquettes_shift_perm)
open YMGap.Continuum.SU2TorusRPLayout (idxOf_map)

/-- The inverse-after-forward identity uses only the original time range. -/
theorem shv_inv_left {β : Type} {N : Nat} (hN : 0 < N) (t : Nat)
    (x : Z4Vertex × β) (hx : x.1.1 < N) :
    shv N (N - t % N) (shv N t x) = x := by
  obtain ⟨⟨a, b, c, d⟩, e⟩ := x
  change ((((a + t) % N + (N - t % N)) % N, b, c, d), e) =
    ((a, b, c, d), e)
  rw [Nat.mod_add_mod, Nat.add_assoc, (cancel_mod hN hx t).1]

/-- The forward-after-inverse identity, including unrestricted periodic shifts. -/
theorem shv_inv_right {β : Type} {N : Nat} (hN : 0 < N) (t : Nat)
    (x : Z4Vertex × β) (hx : x.1.1 < N) :
    shv N t (shv N (N - t % N) x) = x := by
  obtain ⟨⟨a, b, c, d⟩, e⟩ := x
  change ((((a + (N - t % N)) % N + t) % N, b, c, d), e) =
    ((a, b, c, d), e)
  rw [Nat.mod_add_mod, Nat.add_assoc, (cancel_mod hN hx t).2]

private theorem vs_inBox {N : Nat} (hN : 0 < N) (t : Nat)
    (v : Z4Vertex) (hv : InBox N v) : InBox N (vs N t v) := by
  obtain ⟨a, b, c, d⟩ := v
  exact ⟨Nat.mod_lt _ hN, hv.2.1, hv.2.2.1, hv.2.2.2⟩

/-- Time translation retains every physical link in the actual full torus. -/
theorem shv_mem_torusLinks {N : Nat} (hN : 0 < N) (t : Nat)
    (ℓ : Z4Link) (hℓ : ℓ ∈ torusLinks N) : shv N t ℓ ∈ torusLinks N :=
  (mem_torusLinks N _ ℓ.2).mpr
    (vs_inBox hN t ℓ.1 ((mem_torusLinks N ℓ.1 ℓ.2).mp hℓ))

/-- The complete link list is permuted by the literal time shift used by TK. -/
theorem torusLinks_timeShift_perm {N : Nat} (hN : 0 < N) (t : Nat) :
    ((torusLinks N).map (shv N t)).Perm (torusLinks N) := by
  have hinj : ∀ x ∈ torusLinks N, ∀ y ∈ torusLinks N,
      shv N t x = shv N t y → x = y := by
    intro x hx y hy he
    have hi := congrArg (shv N (N - t % N)) he
    rw [shv_inv_left hN t x ((mem_torusLinks N x.1 x.2).mp hx).1,
      shv_inv_left hN t y ((mem_torusLinks N y.1 y.2).mp hy).1] at hi
    exact hi
  refine perm_of_nodup_mem
    (YMGap.Continuum.SU2TimeShift.nodup_map_on (shv N t) _ hinj (torusLinks_nodup N))
    (torusLinks_nodup N) ?_
  intro ℓ
  constructor
  · intro h
    obtain ⟨x, hx, he⟩ := List.mem_map.mp h
    rw [← he]
    exact shv_mem_torusLinks hN t x hx
  · intro hℓ
    exact List.mem_map.mpr ⟨shv N (N - t % N) ℓ,
      shv_mem_torusLinks hN (N - t % N) ℓ hℓ,
      shv_inv_right hN t ℓ ((mem_torusLinks N ℓ.1 ℓ.2).mp hℓ).1⟩

/-- The explicit inverse list used in the OWN-mean transport is a permutation. -/
theorem torusLinks_inverseTimeShift_perm {N : Nat} (hN : 0 < N) (t : Nat) :
    ((torusLinks N).map (shv N (N - t % N))).Perm (torusLinks N) :=
  torusLinks_timeShift_perm hN (N - t % N)

/-- A physical link's index in the inverse-shifted list is exactly its
forward-shifted index in the original list. -/
theorem inverseShift_idxOf {N : Nat} (hN : 0 < N) (t : Nat)
    (ℓ : Z4Link) (hℓ : ℓ ∈ torusLinks N) :
    ((torusLinks N).map (shv N (N - t % N))).idxOf ℓ =
      (torusLinks N).idxOf (shv N t ℓ) := by
  have hshift := shv_mem_torusLinks hN t ℓ hℓ
  have hi := idxOf_map (shv N (N - t % N)) (shv N t ℓ)
    (torusLinks N) hshift (fun x hx he => by
      have hc := congrArg (shv N t) he
      rw [shv_inv_right hN t x ((mem_torusLinks N x.1 x.2).mp hx).1,
        shv_inv_right hN t (shv N t ℓ)
          ((mem_torusLinks N _ _).mp hshift).1] at hc
      exact hc)
  rw [shv_inv_left hN t ℓ ((mem_torusLinks N ℓ.1 ℓ.2).mp hℓ).1] at hi
  exact hi

/-- Time translation also preserves physical temporal and spatial plaquettes. -/
theorem shv_mem_torusPlaquettes {N : Nat} (hN : 0 < N) (t : Nat)
    (p : Z4Plaq) (hp : p ∈ torusPlaquettes N) : shv N t p ∈ torusPlaquettes N :=
  (mem_torusPlaquettes N _ p.2).mpr
    (vs_inBox hN t p.1 ((mem_torusPlaquettes N p.1 p.2).mp hp))

/-- The SAME entire plaquette weight is permuted, with temporal factors retained. -/
theorem torusPlaquettes_timeShift_perm {N : Nat} (hN : 0 < N) (t : Nat) :
    ((torusPlaquettes N).map (shv N t)).Perm (torusPlaquettes N) := by
  have he : (torusPlaquettes N).map (shv N t) =
      (torusPlaquettes N).map (shiftPlaq N (t, 0, 0, 0)) := by
    apply List.map_congr_left
    intro p hp
    obtain ⟨⟨a, b, c, d⟩, P⟩ := p
    have hb := (mem_torusPlaquettes N (a, b, c, d) P).mp hp
    change (((a + t) % N, b, c, d), P) =
      (((a + t) % N, (b + 0) % N, (c + 0) % N, (d + 0) % N), P)
    rw [Nat.add_zero, Nat.add_zero, Nat.add_zero,
      Nat.mod_eq_of_lt hb.2.1, Nat.mod_eq_of_lt hb.2.2.1,
      Nat.mod_eq_of_lt hb.2.2.2]
  rw [he]
  exact torusPlaquettes_shift_perm hN (t, 0, 0, 0)

end YMGap.Continuum.SU2TorusLinksTimeShift

#print axioms YMGap.Continuum.SU2TorusLinksTimeShift.shv_inv_left
#print axioms YMGap.Continuum.SU2TorusLinksTimeShift.shv_inv_right
#print axioms YMGap.Continuum.SU2TorusLinksTimeShift.shv_mem_torusLinks
#print axioms YMGap.Continuum.SU2TorusLinksTimeShift.torusLinks_timeShift_perm
#print axioms YMGap.Continuum.SU2TorusLinksTimeShift.torusLinks_inverseTimeShift_perm
#print axioms YMGap.Continuum.SU2TorusLinksTimeShift.inverseShift_idxOf
#print axioms YMGap.Continuum.SU2TorusLinksTimeShift.shv_mem_torusPlaquettes
#print axioms YMGap.Continuum.SU2TorusLinksTimeShift.torusPlaquettes_timeShift_perm
