/-
# Torus RP (g2): the time shift is a product of two time-coordinate involutions

`rt N c a = (c % N + (N − a)) % N` is the time-coordinate reflection `a ↦ c − a (mod N)`. It is a pure index map,
with no conjugation and no orientation flip. Proved:

* `rt_lt`, `rt_inv`: it maps `[0,N)` to itself and is an involution there.
* `rt_comp`: `rt t (rt 0 a) = (a + t) % N`, i.e. `vs N t = ρ_t ∘ ρ_0`.

This feeds item 4 of the correlator split. Each `ρ_c` is a `QuaternionBlockInvolution` on the torus link order, so
`quaternionHaar_reindex` applies twice. **OPEN**: the block-level packaging (`σ_c i = idxOf (ρ_c (tl[i]))`) and
the Haar-invariance statement for `τ_t`.
-/

import YMGap.Continuum.SU2TorusShiftPerm

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

end YMGap.Continuum.SU2TorusTimeRefl

#print axioms YMGap.Continuum.SU2TorusTimeRefl.rt_inv
#print axioms YMGap.Continuum.SU2TorusTimeRefl.rt_comp
