/-
# Torus RP (d9k): monomials as products of variables; single-term Haar-context equality

* `exp_var`: exponent profile of `polyVar j`.
* `pw_single`, `mp_single`: `pw (x_j) k` and `mp j m = ∏_i x_{j+i}^{m_i}` are single terms with unit coefficient
  and the expected exponent profile.
* `pe_single`: single terms with equal exponent profiles and equivalent coefficients are `PE`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPCore

namespace YMGap.Continuum.SU2TorusRPFixPoly

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (varMono monoMul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2HaarAlgebra (PE)

def pw (x : RatPoly) : Nat → RatPoly
  | 0 => polyOne
  | k + 1 => polyMul x (pw x k)

def mp : Nat → List Nat → RatPoly
  | _, [] => polyOne
  | j, e :: r => polyMul (pw (polyVar j) e) (mp (j + 1) r)

theorem exp_var (j i : Nat) : exponentAt (varMono j) i = if i = j then 1 else 0 := by
  unfold varMono
  rw [YMGap.Continuum.SU2MultiLinkHaarFactorization.exponentAt_replicate_append]
  by_cases h : i < j
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg h]
    by_cases h' : i = j
    · subst h'; rw [if_pos rfl, Nat.sub_self]; rfl
    · rw [if_neg h', show i - j = (i - j - 1) + 1 by omega]; rfl

theorem exp_nil (i : Nat) : exponentAt [] i = 0 := rfl

theorem emm (a b : List Nat) (i : Nat) : exponentAt (monoMul a b) i = exponentAt a i + exponentAt b i :=
  YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.exponentAt_monoMul a b i

theorem pw_single (j : Nat) : ∀ k, ∃ mm : List Nat, ∃ d : Q', pw (polyVar j) k = [(mm, d)] ∧ d.eqv 1 ∧
    ∀ i, exponentAt mm i = if i = j then k else 0
  | 0 => ⟨[], 1, rfl, Q'.eqv_refl _, fun i => by rw [exp_nil]; split <;> rfl⟩
  | k + 1 => by
    obtain ⟨mm, d, e, hd, hx⟩ := pw_single j k
    refine ⟨monoMul (varMono j) mm, 1 * d, by rw [pw, e]; rfl,
      Q'.eqv_trans _ _ _ (Q'.one_mul_eqv d) hd, fun i => ?_⟩
    rw [emm, hx, exp_var]
    by_cases h : i = j
    · rw [if_pos h, if_pos h, if_pos h]; omega
    · rw [if_neg h, if_neg h, if_neg h]

theorem mp_single : ∀ (m : List Nat) (j : Nat), ∃ mm : List Nat, ∃ d : Q', mp j m = [(mm, d)] ∧ d.eqv 1 ∧
    ∀ i, exponentAt mm i = if i < j then 0 else exponentAt m (i - j)
  | [], j => ⟨[], 1, rfl, Q'.eqv_refl _, fun i => by rw [exp_nil, exp_nil]; split <;> rfl⟩
  | e :: r, j => by
    obtain ⟨a, d1, e1, h1, x1⟩ := pw_single j e
    obtain ⟨b, d2, e2, h2, x2⟩ := mp_single r (j + 1)
    refine ⟨monoMul a b, d1 * d2, by rw [mp, e1, e2]; rfl,
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h1) (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv d2) h2),
      fun i => ?_⟩
    rw [emm, x1, x2]
    rcases Nat.lt_trichotomy i j with h | h | h
    · rw [if_neg (by omega), if_pos (by omega), if_pos h]
    · subst h; rw [if_pos rfl, if_pos (by omega), if_neg (by omega), Nat.sub_self]; rfl
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show i - j = (i - (j + 1)) + 1 by omega, Nat.zero_add]
      rfl

theorem pe_single (n : Nat) {a b : List Nat} {c d : Q'} (he : ∀ i, exponentAt a i = exponentAt b i)
    (hc : c.eqv d) : PE n [(a, c)] [(b, d)] := fun m => by
  show (c * YMGap.Continuum.BF4GeometricHaarMehlerProjection.quaternionHaarMono n (monoMul m a) + 0).eqv
    (d * YMGap.Continuum.BF4GeometricHaarMehlerProjection.quaternionHaarMono n (monoMul m b) + 0)
  rw [YMGap.Continuum.SU2TorusRPCore.mono_congr n (m := monoMul m a) (m' := monoMul m b)
    (fun i => by rw [emm, emm, he])]
  exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ hc) (Q'.eqv_refl _)

end YMGap.Continuum.SU2TorusRPFixPoly

#print axioms YMGap.Continuum.SU2TorusRPFixPoly.mp_single
#print axioms YMGap.Continuum.SU2TorusRPFixPoly.pe_single
