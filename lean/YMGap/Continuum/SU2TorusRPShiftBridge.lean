/-
# Torus RP assembly (d3a): a half-swapping block involution acts as `shiftPoly`

If `σ` is an involution of `a + a` blocks with `σ k = k + a` for `k < a` (so the link list is ordered as
`L ++ Θ(L)`), then on polynomials supported in the first `a` blocks, `reindex σ X ≈PE shiftPoly a X`.
This is the bridge from the geometric Θpoly (`thetaInv`) to the abstract `shiftPoly` used in
`rp_full` / `wilson_rp_qfull`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (still to do: the torus link ordering `L ++ Θ(L) ++ crossing`, the
crossing split and the final `hW`).
-/

import YMGap.Continuum.SU2TorusRPThetaProd

namespace YMGap.Continuum.SU2TorusRPShiftBridge

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
  (QuaternionBlockInvolution reindexQuaternionPolynomial reindexQuaternionExponents exponentAt_reindexQuaternionExponents)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_append pe_refl)
open YMGap.Continuum.SU2MultiLinkHaarFactorization (shiftPoly exponentAt_replicate_append exponentAt_of_length_le)
open YMGap.Continuum.SU2TorusRPCore (Sup)
open YMGap.Continuum.SU2TorusRPReindex (exp_out pe_mono)

variable {a : Nat} (σ : QuaternionBlockInvolution (a + a)) (hσ : ∀ k, k < a → σ.map k = k + a)
include hσ

theorem exp_swap (m : List Nat) (hm : m.length ≤ 4 * a) (i : Nat) :
    exponentAt (reindexQuaternionExponents σ m) i = exponentAt (List.replicate (4 * a) 0 ++ m) i := by
  rw [exponentAt_replicate_append]
  by_cases h1 : i < 4 * a
  · rw [if_pos h1, exponentAt_reindexQuaternionExponents σ _ (by omega), hσ _ (by omega)]
    exact exponentAt_of_length_le _ _ (by omega)
  · rw [if_neg h1]
    by_cases h2 : i < 4 * (a + a)
    · rw [exponentAt_reindexQuaternionExponents σ _ h2]
      have hk : σ.map (i / 4 - a) = i / 4 := by rw [hσ _ (by omega)]; omega
      have hs : σ.map (i / 4) = i / 4 - a := by
        have := σ.involutive (i / 4 - a) (by omega); rw [hk] at this; exact this
      rw [hs, show 4 * (i / 4 - a) + i % 4 = i - 4 * a by omega]
    · rw [exp_out σ m i (by omega), exponentAt_of_length_le _ _ (by omega)]

theorem reindex_shift : ∀ X : RatPoly, Sup a X →
    PE (a + a) (reindexQuaternionPolynomial σ X) (shiftPoly a X)
  | [], _ => pe_refl _ _
  | t :: X, hX => by
    show PE (a + a) ([(reindexQuaternionExponents σ t.1, t.2)] ++ reindexQuaternionPolynomial σ X)
      ([(List.replicate (4 * a) 0 ++ t.1, t.2)] ++ shiftPoly a X)
    exact pe_append _ (pe_mono _ t.2 (exp_swap σ hσ t.1 (hX t (List.mem_cons_self ..))))
      (reindex_shift X fun s hs => hX s (List.mem_cons_of_mem _ hs))

end YMGap.Continuum.SU2TorusRPShiftBridge

#print axioms YMGap.Continuum.SU2TorusRPShiftBridge.reindex_shift
