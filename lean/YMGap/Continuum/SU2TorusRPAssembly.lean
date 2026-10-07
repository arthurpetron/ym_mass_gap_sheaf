/-
# Torus RP assembly (d3f): the conclusion step, Θ realised as a conj-twisted shift

`rp_conj_assembly`: let `C` be a Haar-invariant `RingSub` on `a + a` blocks (in use, the second-half temporal conj).
Suppose `C` fixes `F` and `Wp` (both supported in the first half) and turns their Θ-images `ThF`, `ThWp` into
`shiftPoly a F` and `shiftPoly a Wp`. If `C Wc` is an RPK, then
  `0 ≤ ∫ (ThF · F) · ((Wp · ThWp) · Wc)`.
This discharges `rp_full`'s `hW` for an integrand in the factorised form `torus_factor` produces, given RPK of the
(conj-twisted) crossing part.

`theta_C_shift`: the twist hypotheses hold for `C = sign(above (4a) T)` and `Θ = sign T ∘ reindex σ` whenever `σ` is the
half shift on the first `a` blocks (the `L ++ Θ(L)` layout, `half_map`).

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.** Still to do: the crossing split (the crossing links are Θ-fixed, so
the actual torus is not yet in the `L ++ Θ(L)` layout) and RPK of the crossing part.
-/

import YMGap.Continuum.SU2TorusRPHalfConj

namespace YMGap.Continuum.SU2TorusRPAssembly

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_symm pe_refl pe_haar)
open YMGap.Continuum.SU2TorusRPSubst (RingSub pe_mul2)
open YMGap.Continuum.SU2MultiLinkHaarFactorization (shiftPoly)
open YMGap.Continuum.SU2TorusRPCore (Sup RPK rp_full)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
  (QuaternionBlockInvolution signSelectedPolynomial reindexQuaternionPolynomial reindexQuaternionExponents
   exponentAt_reindexQuaternionExponents)
open YMGap.Continuum.SU2TorusRPHalfConj (above sign_second_half sign_first_half)

theorem rp_conj_assembly {a : Nat} (C : RatPoly → RatPoly)
    (hCh : ∀ X, (quaternionHaar (a + a) (C X)).eqv (quaternionHaar (a + a) X)) (hC : RingSub (a + a) C)
    (F Wp Wc ThF ThWp : RatPoly) (hF : Sup a F) (hWp : Sup a Wp)
    (hCF : PE (a + a) (C F) F) (hCWp : PE (a + a) (C Wp) Wp)
    (hThF : PE (a + a) (C ThF) (shiftPoly a F)) (hThWp : PE (a + a) (C ThWp) (shiftPoly a Wp))
    (hWc : RPK a (C Wc)) :
    (0 : Q') ≤ quaternionHaar (a + a) (polyMul (polyMul ThF F) (polyMul (polyMul Wp ThWp) Wc)) := by
  have hpe : PE (a + a) (C (polyMul (polyMul ThF F) (polyMul (polyMul Wp ThWp) Wc)))
      (polyMul (polyMul (shiftPoly a F) F) (polyMul (polyMul Wp (shiftPoly a Wp)) (C Wc))) :=
    pe_trans _ (hC.mul _ _) (pe_mul2 _
      (pe_trans _ (hC.mul _ _) (pe_mul2 _ hThF hCF))
      (pe_trans _ (hC.mul _ _) (pe_mul2 _ (pe_trans _ (hC.mul _ _) (pe_mul2 _ hCWp hThWp)) (pe_refl _ _))))
  have h0 := rp_full F Wp (C Wc) _ hF hWp hWc (pe_refl _ _)
  exact Q'.le_trans' _ _ _ h0 (Q'.le_of_eqv (Q'.eqv_symm
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (hCh _)) (pe_haar _ hpe))))

/-- Reindexing by a half shift leaves no exponent in the first `4a` coordinates. -/
theorem reindex_low_zero {a : Nat} (σ : QuaternionBlockInvolution (a + a)) (hσ : ∀ k, k < a → σ.map k = k + a)
    (m : List Nat) (hm : m.length ≤ 4 * a) (c : Nat) (hc : c < 4 * a) :
    exponentAt (reindexQuaternionExponents σ m) c = 0 := by
  rw [exponentAt_reindexQuaternionExponents σ _ (by omega), hσ _ (by omega)]
  exact YMGap.Continuum.SU2MultiLinkHaarFactorization.exponentAt_of_length_le _ _ (by omega)

/-- **Twist hypotheses for the geometric Θ.** -/
theorem theta_C_shift {a : Nat} (σ : QuaternionBlockInvolution (a + a)) (hσ : ∀ k, k < a → σ.map k = k + a)
    (T : Nat → Bool) (X : RatPoly) (hX : Sup a X) :
    PE (a + a) (signSelectedPolynomial (4 * (a + a)) (above (4 * a) T)
        (signSelectedPolynomial (4 * (a + a)) T (reindexQuaternionPolynomial σ X))) (shiftPoly a X) := by
  have hlow : ∀ t ∈ reindexQuaternionPolynomial σ X, ∀ c, c < 4 * a → exponentAt t.1 c = 0 := by
    intro t ht c hc
    simp only [reindexQuaternionPolynomial, List.mem_map] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    exact reindex_low_zero σ hσ s.1 (hX s hs) c hc
  rw [sign_second_half _ (4 * a) T _ hlow]
  exact SU2TorusRPThetaShift.theta_shift σ hσ _ _ X hX

theorem C_fixes {a : Nat} (T : Nat → Bool) (X : RatPoly) (hX : Sup a X) :
    PE (a + a) (signSelectedPolynomial (4 * (a + a)) (above (4 * a) T) X) X :=
  sign_first_half _ _ _ T X hX

end YMGap.Continuum.SU2TorusRPAssembly

#print axioms YMGap.Continuum.SU2TorusRPAssembly.rp_conj_assembly
#print axioms YMGap.Continuum.SU2TorusRPAssembly.theta_C_shift
#print axioms YMGap.Continuum.SU2TorusRPAssembly.C_fixes
