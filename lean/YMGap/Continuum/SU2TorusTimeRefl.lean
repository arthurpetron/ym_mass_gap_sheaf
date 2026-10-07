/-
# Torus RP (g2): the time shift is a product of two time-coordinate involutions

`rt N c a = (c % N + (N − a)) % N` is the time-coordinate reflection `a ↦ c − a (mod N)`. It is a pure index map,
with no conjugation and no orientation flip. Proved:

* `rt_lt`, `rt_inv`: it maps `[0,N)` to itself and is an involution there.
* `rt_comp`: `rt t (rt 0 a) = (a + t) % N`, i.e. `vs N t = ρ_t ∘ ρ_0`.

This feeds item 4 of the correlator split. Each `ρ_c` is a `QuaternionBlockInvolution` on the torus link order, so
`quaternionHaar_reindex` applies twice. Also proved: `rl_mem`, `rl_inv`, `rl_comp` at link level, and
the block involution `sigma N c` (via `linkInv`). **OPEN**: the Haar-invariance statement for `τ_t = σ_t ∘ σ_0`.
-/

import YMGap.Continuum.SU2TorusShiftPerm
import YMGap.Continuum.SU2TorusRPThetaPoly

namespace YMGap.Continuum.SU2TorusTimeRefl

set_option autoImplicit false

open YMGap.Continuum.SU2TorusShiftPerm (m2)

def rt (N c a : Nat) : Nat := (c % N + (N - a)) % N

theorem rt_lt (N c a : Nat) (hN : 0 < N) : rt N c a < N := Nat.mod_lt _ hN

theorem rt_val (N c a : Nat) (hN : 0 < N) (ha : a < N) :
    rt N c a = if c % N + (N - a) < N then c % N + (N - a) else c % N + (N - a) - N := by
  have := Nat.mod_lt c hN
  exact m2 _ _ (by omega)

theorem rt_inv (N c a : Nat) (hN : 0 < N) (ha : a < N) : rt N c (rt N c a) = a := by
  have hr := Nat.mod_lt c hN
  rw [rt_val N c (rt N c a) hN (rt_lt N c a hN), rt_val N c a hN ha]
  split <;> split <;> omega

theorem rt_comp (N t a : Nat) (hN : 0 < N) (ha : a < N) : rt N t (rt N 0 a) = (a + t) % N := by
  have hr := Nat.mod_lt t hN
  rw [rt_val N t (rt N 0 a) hN (rt_lt N 0 a hN), rt_val N 0 a hN ha, Nat.zero_mod,
    YMGap.Continuum.SU2TorusShiftPerm.shift_eq N t a hN ha]
  split <;> split <;> split <;> omega

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry

/-- Link-level time-coordinate involution `ρ_c` (pure reindex, direction kept). -/
def rl (N c : Nat) (ℓ : Z4Link) : Z4Link := ((rt N c ℓ.1.1, ℓ.1.2), ℓ.2)

theorem rl_mem (N c : Nat) (hN : 0 < N) (ℓ : Z4Link) (h : ℓ ∈ torusLinks N) : rl N c ℓ ∈ torusLinks N := by
  obtain ⟨⟨a, b, c', d⟩, e⟩ := ℓ
  have ⟨_, h2, h3, h4⟩ := (mem_torusLinks N _ e).1 h
  exact (mem_torusLinks N _ e).2 ⟨rt_lt N c a hN, h2, h3, h4⟩

theorem rl_inv (N c : Nat) (hN : 0 < N) (ℓ : Z4Link) (h : ℓ ∈ torusLinks N) : rl N c (rl N c ℓ) = ℓ := by
  obtain ⟨⟨a, b, c', d⟩, e⟩ := ℓ
  have h1 := ((mem_torusLinks N _ e).1 h).1
  show ((rt N c (rt N c a), b, c', d), e) = _
  rw [rt_inv N c a hN h1]

theorem rl_comp (N t : Nat) (hN : 0 < N) (ℓ : Z4Link) (h : ℓ ∈ torusLinks N) :
    rl N t (rl N 0 ℓ) = YMGap.Continuum.SU2TimeShift.shv N t ℓ := by
  obtain ⟨⟨a, b, c', d⟩, e⟩ := ℓ
  have h1 := ((mem_torusLinks N _ e).1 h).1
  show ((rt N t (rt N 0 a), b, c', d), e) = _
  rw [rt_comp N t a hN h1]; rfl

/-- The block involution `σ_c` on the torus link order. -/
def sigma (N c : Nat) (hN : 0 < N) :=
  YMGap.Continuum.SU2TorusRPThetaPoly.linkInv (torusLinks N) (rl N c) (torusLinks_nodup N) (rl_mem N c hN) (rl_inv N c hN)

end YMGap.Continuum.SU2TorusTimeRefl

#print axioms YMGap.Continuum.SU2TorusTimeRefl.rt_inv
#print axioms YMGap.Continuum.SU2TorusTimeRefl.rt_comp
#print axioms YMGap.Continuum.SU2TorusTimeRefl.rl_comp
