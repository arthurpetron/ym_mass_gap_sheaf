/-
# Torus RP (d6a): lifting PE to more blocks

`pe_lift`: if `X, Y` are supported on the first `n` blocks and `PE n X Y`, then `PE (n + e) X Y`. This moves
`thetaPoly`/`torus_factor` statements (on `links.length` blocks) to the extended carrier with fresh split
partners.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPSplitRP

namespace YMGap.Continuum.SU2TorusRPPELift

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HaarAlgebra (PE phi)
open YMGap.Continuum.SU2MultiLinkHaarFactorization (mono_factor exponentAt_drop exponentAt_replicate_append
  exponentAt_of_length_le)
open YMGap.Continuum.SU2TorusRPCore (Sup length_monoMul)

theorem exponentAt_take : ∀ (k : Nat) (m : List Nat) (i : Nat),
    exponentAt (m.take k) i = if i < k then exponentAt m i else 0
  | 0, m, i => by rw [if_neg (by omega)]; rfl
  | k + 1, [], i => by
      show exponentAt [] i = _
      by_cases h : i < k + 1
      · rw [if_pos h]
      · rw [if_neg h]; rfl
  | k + 1, x :: xs, 0 => by rw [if_pos (by omega)]; rfl
  | k + 1, x :: xs, i + 1 => by
      show exponentAt (xs.take k) i = _
      rw [exponentAt_take k xs i]
      by_cases h : i < k
      · rw [if_pos h, if_pos (by omega)]; rfl
      · rw [if_neg h, if_neg (by omega)]

theorem row (n e : Nat) (m : List Nat) (s : List Nat) (hs : s.length ≤ 4 * n) :
    (quaternionHaarMono (n + e) (monoMul m s)).eqv
      (quaternionHaarMono n (monoMul (m.take (4 * n)) s) * quaternionHaarMono e (m.drop (4 * n))) := by
  have hl : (monoMul (m.take (4 * n)) s).length ≤ 4 * n := by
    rw [length_monoMul, List.length_take]; exact Nat.max_le.mpr ⟨Nat.min_le_left _ _, hs⟩
  rw [YMGap.Continuum.SU2TorusRPCore.mono_congr (n + e) (m := monoMul m s)
    (m' := monoMul (monoMul (m.take (4 * n)) s) (List.replicate (4 * n) 0 ++ m.drop (4 * n))) (fun i => by
      simp only [YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.exponentAt_monoMul,
        exponentAt_replicate_append, exponentAt_take, exponentAt_drop]
      by_cases h : i < 4 * n
      · rw [if_pos h, if_pos h]; omega
      · rw [if_neg h, if_neg h, exponentAt_of_length_le s i (by omega), show 4 * n + (i - 4 * n) = i by omega]
        omega)]
  exact mono_factor n e _ _ hl

theorem phi_lift (n e : Nat) (m : List Nat) : ∀ X : RatPoly, Sup n X →
    (phi (n + e) X m).eqv (phi n X (m.take (4 * n)) * quaternionHaarMono e (m.drop (4 * n)))
  | [], _ => Q'.eqv_symm (Q'.zero_mul_eqv _)
  | t :: X, h => by
      change (t.2 * quaternionHaarMono (n + e) (monoMul m t.1) + phi (n + e) X m).eqv
        ((t.2 * quaternionHaarMono n (monoMul (m.take (4 * n)) t.1) + phi n X (m.take (4 * n))) *
          quaternionHaarMono e (m.drop (4 * n)))
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ (row n e m t.1 (h t (List.mem_cons_self ..))))
        (phi_lift n e m X fun s hs => h s (List.mem_cons_of_mem _ hs))) ?_
      refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _) (Q'.add_eqv_congr' ?_ (Q'.eqv_refl _)))
      exact Q'.mul_assoc_eqv _ _ _

theorem pe_lift (n e : Nat) {X Y : RatPoly} (h : PE n X Y) (hX : Sup n X) (hY : Sup n Y) : PE (n + e) X Y :=
  fun m => Q'.eqv_trans _ _ _ (phi_lift n e m X hX)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (h _)) (Q'.eqv_symm (phi_lift n e m Y hY)))

end YMGap.Continuum.SU2TorusRPPELift

#print axioms YMGap.Continuum.SU2TorusRPPELift.pe_lift
