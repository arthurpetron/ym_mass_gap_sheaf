/-
# Torus RP assembly (b7): block reindexing respects Haar-context equivalence on supported polynomials

* `phi_reindex`: for `X` on the `n` blocks and a context `m` with no exponent beyond `4n`,
  `phi n (σ X) m ≈ phi n X (σ m)`. If `m` has an exponent beyond `4n`, every moment of `σ X` in context `m` vanishes
  (`phi_reindex_out`).
* `reindex_peCongrOn`: `Sup n X → Sup n Y → PE n X Y → PE n (σ X) (σ Y)`.
* `PECongrOn n S`: the supported variant of `PECongr`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (head-shear `PECongrOn`, geometry (c) and assembly (d) remain).
-/

import YMGap.Continuum.SU2TorusRPConjCongr

namespace YMGap.Continuum.SU2TorusRPReindexCongr

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
  (QuaternionBlockInvolution reindexQuaternionPolynomial reindexQuaternionExponents
   reindexQuaternionExponents_length exponentAt_reindexQuaternionExponents quaternionHaarMono_reindex)
open YMGap.Continuum.SU2HaarAlgebra (PE phi sm sm_congr sm_map)
open YMGap.Continuum.SU2MultiLinkHaarFactorization (exponentAt_drop allZero_iff exponentAt_of_length_le)
open YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal (exponentAt_monoMul)
open YMGap.Continuum.SU2TorusRPCore (Sup mono_congr)
open YMGap.Continuum.SU2TorusRPReindex (exp_out)

/-- Supported variant of `PECongr`. -/
def PECongrOn (n : Nat) (S : RatPoly → RatPoly) : Prop :=
  ∀ {X Y}, Sup n X → Sup n Y → PE n X Y → PE n (S X) (S Y)

variable {n : Nat} (σ : QuaternionBlockInvolution n)

theorem sm_zero' {β : Type} (f : β → Q') : ∀ l : List β, (∀ x ∈ l, (f x).eqv 0) → (sm f l).eqv 0
  | [], _ => Q'.eqv_refl _
  | x :: l, h => Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (h x (List.mem_cons_self ..))
      (sm_zero' f l fun y hy => h y (List.mem_cons_of_mem _ hy))) (by decide)

theorem allZero_mul (m : List Nat) (x : List Nat) :
    allZero ((monoMul m (reindexQuaternionExponents σ x)).drop (4 * n)) = allZero (m.drop (4 * n)) := by
  apply Bool.eq_iff_iff.mpr
  rw [allZero_iff, allZero_iff]
  simp only [exponentAt_drop, exponentAt_monoMul]
  simp only [fun i => exp_out σ x (4 * n + i) (by omega), Nat.add_zero]

theorem term_out (m : List Nat) (hm : allZero (m.drop (4 * n)) = false) (x : List Nat) :
    quaternionHaarMono n (monoMul m (reindexQuaternionExponents σ x)) = 0 := by
  unfold quaternionHaarMono; rw [allZero_mul, hm]; rfl

theorem phi_reindex_out (X : RatPoly) (m : List Nat) (hm : allZero (m.drop (4 * n)) = false) :
    (phi n (reindexQuaternionPolynomial σ X) m).eqv 0 := by
  unfold phi reindexQuaternionPolynomial; rw [sm_map]
  exact sm_zero' _ X fun x _ => by
    show (x.2 * quaternionHaarMono n (monoMul m (reindexQuaternionExponents σ x.1))).eqv 0
    rw [term_out σ m hm]; exact Q'.mul_zero_eqv _

theorem term_in (m : List Nat) (hm : allZero (m.drop (4 * n)) = true) (x : List Nat) (hx : x.length ≤ 4 * n) :
    (quaternionHaarMono n (monoMul m (reindexQuaternionExponents σ x))).eqv
      (quaternionHaarMono n (monoMul (reindexQuaternionExponents σ m) x)) := by
  have hz := (allZero_iff _).mp hm
  have hlen : (monoMul (reindexQuaternionExponents σ m) x).length ≤ 4 * n := by
    rw [YMGap.Continuum.SU2TorusRPCore.length_monoMul, reindexQuaternionExponents_length]; omega
  rw [mono_congr n (m' := reindexQuaternionExponents σ (monoMul (reindexQuaternionExponents σ m) x)) (fun i => by
    by_cases hi : i < 4 * n
    · rw [exponentAt_monoMul, exponentAt_reindexQuaternionExponents σ _ hi,
        exponentAt_reindexQuaternionExponents σ _ hi, exponentAt_monoMul,
        exponentAt_reindexQuaternionExponents σ _ (by have := σ.map_lt (i / 4) (by omega); omega)]
      have h1 : (4 * σ.map (i / 4) + i % 4) / 4 = σ.map (i / 4) := by omega
      have h2 : (4 * σ.map (i / 4) + i % 4) % 4 = i % 4 := by omega
      rw [h1, h2, σ.involutive _ (by omega), show 4 * (i / 4) + i % 4 = i by omega]
    · rw [exponentAt_monoMul, exp_out σ x i (by omega), exp_out σ _ i (by omega)]
      have := hz (i - 4 * n); rw [exponentAt_drop, show 4 * n + (i - 4 * n) = i by omega] at this
      omega)]
  exact quaternionHaarMono_reindex σ _ hlen

theorem phi_reindex (X : RatPoly) (hX : Sup n X) (m : List Nat) (hm : allZero (m.drop (4 * n)) = true) :
    (phi n (reindexQuaternionPolynomial σ X) m).eqv (phi n X (reindexQuaternionExponents σ m)) := by
  unfold phi reindexQuaternionPolynomial; rw [sm_map]
  exact sm_congr X fun x hx => Q'.mul_eqv_congr_left _ _ _ (term_in σ m hm x.1 (hX x hx))

theorem reindex_peCongrOn : PECongrOn n (reindexQuaternionPolynomial σ) := fun hX hY h m => by
  cases hm : allZero (m.drop (4 * n))
  · exact Q'.eqv_trans _ _ _ (phi_reindex_out σ _ m hm) (Q'.eqv_symm (phi_reindex_out σ _ m hm))
  · exact Q'.eqv_trans _ _ _ (phi_reindex σ _ hX m hm)
      (Q'.eqv_trans _ _ _ (h _) (Q'.eqv_symm (phi_reindex σ _ hY m hm)))

end YMGap.Continuum.SU2TorusRPReindexCongr

#print axioms YMGap.Continuum.SU2TorusRPReindexCongr.reindex_peCongrOn
