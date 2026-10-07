/-
# Torus RP assembly (b2, part): block reindexing is a `RingSub`, and its action on link variables

* `pe_mono`: two single-term polynomials with the same exponent at every coordinate are `PE`.
* `reindex_ringSub σ`: `reindexQuaternionPolynomial σ` is a `RingSub n` (literal on `mul/add/smul/neg`; `one` up to
  padding).
* `reindex_var`: `σ` sends coordinate `4b+c` to `4σ(b)+c`, so `qsub (reindex σ) (coordinateVariable b) ≡
  coordinateVariable (σ b)`. Together with `SU2TorusRPSubst.TK_word_sub`, this transports the Wilson integrand
  through any block involution. It is used to bring the torus link list into the half-split order.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.** Still to do: `RingSub` instances for the split shears and the conj flip,
the geometry (c) and the assembly (d).
-/

import YMGap.Continuum.SU2TorusRPSubst
import YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport

namespace YMGap.Continuum.SU2TorusRPReindex

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul varMono)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HaarAlgebra (PE pe_refl)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
  (QuaternionBlockInvolution reindexQuaternionPolynomial reindexQuaternionExponents
   reindexQuaternionExponents_length exponentAt_reindexQuaternionExponents reindexQuaternionPolynomial_mul
   reindexQuaternionPolynomial_add reindexQuaternionPolynomial_smul reindexQuaternionPolynomial_neg)
open YMGap.Continuum.SU2TorusRPSubst (RingSub QPE qsub)

theorem pe_mono (n : Nat) {e e' : List Nat} (c : Q') (h : ∀ i, exponentAt e i = exponentAt e' i) :
    PE n [(e, c)] [(e', c)] := fun m => by
  show (c * quaternionHaarMono n (monoMul m e) + 0).eqv (c * quaternionHaarMono n (monoMul m e') + 0)
  rw [YMGap.Continuum.SU2TorusRPCore.mono_congr n (m := monoMul m e) (m' := monoMul m e') (fun i => by
    rw [YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.exponentAt_monoMul,
      YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.exponentAt_monoMul, h i])]
  exact Q'.eqv_refl _

theorem exp_out {n : Nat} (σ : QuaternionBlockInvolution n) (m : List Nat) (i : Nat) (hi : 4 * n ≤ i) :
    exponentAt (reindexQuaternionExponents σ m) i = 0 :=
  YMGap.Continuum.SU2MultiLinkHaarFactorization.exponentAt_of_length_le _ _
    (by rw [reindexQuaternionExponents_length]; exact hi)

theorem reindex_ringSub {n : Nat} (σ : QuaternionBlockInvolution n) :
    RingSub n (reindexQuaternionPolynomial σ) where
  mul p q := by rw [reindexQuaternionPolynomial_mul]; exact pe_refl _ _
  add p q := by rw [reindexQuaternionPolynomial_add]; exact pe_refl _ _
  smul c p := by rw [reindexQuaternionPolynomial_smul]; exact pe_refl _ _
  neg p := by rw [reindexQuaternionPolynomial_neg]; exact pe_refl _ _
  one := pe_mono n 1 fun i => by
    by_cases hi : i < 4 * n
    · rw [exponentAt_reindexQuaternionExponents σ [] hi]; simp [exponentAt]
    · rw [exp_out σ [] i (by omega)]; simp [exponentAt]

open YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport (exponentAt_varMono) in
theorem reindex_polyVar {n : Nat} (σ : QuaternionBlockInvolution n) (b c : Nat) (hb : b < n) (hc : c < 4) :
    PE n (reindexQuaternionPolynomial σ (polyVar (4 * b + c))) (polyVar (4 * σ.map b + c)) := by
  have hσb := σ.map_lt b hb
  refine pe_mono n 1 fun i => ?_
  rw [exponentAt_varMono]
  by_cases hi : i < 4 * n
  · rw [exponentAt_reindexQuaternionExponents σ _ hi, exponentAt_varMono]
    have hq := σ.map_lt (i / 4) (by omega)
    have hinv := σ.involutive (i / 4) (by omega)
    have hinvb := σ.involutive b hb
    by_cases h1 : i = 4 * σ.map b + c
    · subst h1
      have e1 : (4 * σ.map b + c) / 4 = σ.map b := by omega
      have e2 : (4 * σ.map b + c) % 4 = c := by omega
      rw [e1, e2, hinvb]; simp
    · rw [if_neg h1, if_neg]
      intro h2
      have hb' : σ.map (i / 4) = b := by omega
      have hc' : i % 4 = c := by omega
      apply h1; rw [← hb', hinv]; omega
  · rw [exp_out σ _ i (by omega), if_neg (by omega)]

theorem reindex_coord {n : Nat} (σ : QuaternionBlockInvolution n) (b : Nat) (hb : b < n) :
    QPE n (qsub (reindexQuaternionPolynomial σ) (PolyQuaternion.coordinateVariable b))
      (PolyQuaternion.coordinateVariable (σ.map b)) :=
  ⟨by simpa using reindex_polyVar σ b 0 hb (by decide), reindex_polyVar σ b 1 hb (by decide),
   reindex_polyVar σ b 2 hb (by decide), reindex_polyVar σ b 3 hb (by decide)⟩

end YMGap.Continuum.SU2TorusRPReindex

#print axioms YMGap.Continuum.SU2TorusRPReindex.reindex_ringSub
#print axioms YMGap.Continuum.SU2TorusRPReindex.reindex_coord
