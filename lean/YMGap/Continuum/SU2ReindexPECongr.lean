/-
# Transfer matrix (2a): block reindexing respects Haar-context equivalence on supported polynomials

ADDITIVE.  **Labels:** algebra only, valid for every coupling; also true for U(1), not gap evidence.
Realizer's files are imported, not edited.

`SU2TorusRPConj` lists `PECongr n (reindexQuaternionPolynomial σ)` as OPEN.  Without support it is
**false**: `reindexQuaternionExponents` truncates to `4n` coordinates, so it can turn a monomial
that is Haar-null (because of an exponent beyond `4n`) into a non-null one (`pecongr_fails`).
What holds, and what the slice/transfer assembly needs, is the supported version:

* `phi_null`: if `m` has a nonzero exponent beyond `4n`, then `phi n Z m ≈ 0` for every `Z`.
* `phi_reindex`: for X supported on `n` blocks and `m` zero beyond `4n`,
  `phi n (σ X) m ≈ phi n X (σ m)`.
* `pe_reindex`: `Sup n X → Sup n Y → PE n X Y → PE n (σ X) (σ Y)`.
* `sup_reindex`: `σ X` is again supported, so the statement composes.
-/

import YMGap.Continuum.SU2TorusRPConj

namespace YMGap.Continuum.SU2ReindexPECongr

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2HaarAlgebra (PE phi sm)
open YMGap.Continuum.SU2MultiLinkHaarFactorization (allZero_iff exponentAt_of_length_le)
open YMGap.Continuum.SU2TorusRPCore (Sup mono_congr length_monoMul)

variable {n : Nat} (σ : QuaternionBlockInvolution n)

local notation "rσ" => reindexQuaternionPolynomial σ
local notation "eσ" => reindexQuaternionExponents σ

theorem exp_out (m : List Nat) (i : Nat) (hi : 4 * n ≤ i) : exponentAt (eσ m) i = 0 :=
  exponentAt_of_length_le _ _ (by rw [reindexQuaternionExponents_length]; exact hi)

/-- A context with a nonzero exponent beyond `4n` kills every term. -/
theorem mono_null (m e : List Nat) (hm : allZero (m.drop (4 * n)) = false) :
    quaternionHaarMono n (monoMul m e) = 0 := by
  unfold quaternionHaarMono
  have : allZero ((monoMul m e).drop (4 * n)) = false := by
    cases h : allZero ((monoMul m e).drop (4 * n))
    · rfl
    · have h1 := (allZero_iff _).mp h
      have : allZero (m.drop (4 * n)) = true := (allZero_iff _).mpr fun i => by
        have := h1 i
        rw [exponentAt_drop, exponentAt_monoMul] at this
        rw [exponentAt_drop]; omega
      rw [this] at hm; exact absurd hm (by decide)
  rw [this]; rfl

theorem phi_null (m : List Nat) (hm : allZero (m.drop (4 * n)) = false) :
    ∀ Z : RatPoly, (phi n Z m).eqv 0
  | [] => Q'.eqv_refl _
  | t :: Z => by
    show (t.2 * quaternionHaarMono n (monoMul m t.1) + sm _ Z).eqv 0
    rw [mono_null m t.1 hm]
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (YMGap.Constructive.Q'.mul_zero_eqv _) (phi_null m hm Z))
      (by decide)

/-- Index identity `σ̂(σ̂ i) = i` on coordinates. -/
theorem idx_invol (i : Nat) (hi : i < 4 * n) :
    4 * σ.map ((4 * σ.map (i / 4) + i % 4) / 4) + (4 * σ.map (i / 4) + i % 4) % 4 = i := by
  have h1 : (4 * σ.map (i / 4) + i % 4) / 4 = σ.map (i / 4) := by omega
  have h2 : (4 * σ.map (i / 4) + i % 4) % 4 = i % 4 := by omega
  rw [h1, h2, σ.involutive _ (by omega)]
  omega

theorem idx_lt (i : Nat) (hi : i < 4 * n) : 4 * σ.map (i / 4) + i % 4 < 4 * n := by
  have := σ.map_lt (i / 4) (by omega)
  omega

/-- Term identity: `H(m · σe) ≈ H(σm · e)` for `m` zero beyond `4n` and `e` supported. -/
theorem term_reindex (m e : List Nat) (hm : allZero (m.drop (4 * n)) = true) (he : e.length ≤ 4 * n) :
    (quaternionHaarMono n (monoMul m (eσ e))).eqv (quaternionHaarMono n (monoMul (eσ m) e)) := by
  have hz := (allZero_iff _).mp hm
  have hmz : ∀ i, 4 * n ≤ i → exponentAt m i = 0 := fun i hi => by
    have := hz (i - 4 * n); rw [exponentAt_drop, show 4 * n + (i - 4 * n) = i by omega] at this; exact this
  let m' := m.take (4 * n)
  have hm' : ∀ i, exponentAt m' i = if i < 4 * n then exponentAt m i else 0 := fun i => by
    split
    · simp [m', exponentAt, List.getD_eq_getElem?_getD, *]
    · exact exponentAt_of_length_le _ _ (by simp [m']; omega)
  let A := monoMul m' (eσ e)
  have hA : A.length ≤ 4 * n := by
    rw [length_monoMul, reindexQuaternionExponents_length]
    have : m'.length ≤ 4 * n := by simp only [m', List.length_take]; exact Nat.min_le_left _ _
    omega
  have e1 : quaternionHaarMono n (monoMul m (eσ e)) = quaternionHaarMono n A :=
    mono_congr n fun i => by
      rw [exponentAt_monoMul, exponentAt_monoMul, hm' i]
      split
      · rfl
      · rw [hmz i (by omega)]
  have e2 : quaternionHaarMono n (eσ A) = quaternionHaarMono n (monoMul (eσ m) e) :=
    mono_congr n fun i => by
      rw [exponentAt_monoMul]
      by_cases hi : i < 4 * n
      · rw [exponentAt_reindexQuaternionExponents σ A hi]
        show exponentAt (monoMul m' (eσ e)) _ = _
        rw [exponentAt_monoMul, hm', if_pos (idx_lt σ i hi),
          exponentAt_reindexQuaternionExponents σ e (idx_lt σ i hi), idx_invol σ i hi,
          exponentAt_reindexQuaternionExponents σ m hi]
      · rw [exp_out σ A i (by omega), exp_out σ m i (by omega), exponentAt_of_length_le e i (by omega)]
  rw [e1, ← e2]
  exact Q'.eqv_symm (quaternionHaarMono_reindex σ A hA)

theorem phi_reindex (m : List Nat) (hm : allZero (m.drop (4 * n)) = true) :
    ∀ X : RatPoly, Sup n X → (phi n (rσ X) m).eqv (phi n X (eσ m))
  | [], _ => Q'.eqv_refl _
  | t :: X, hX => by
    show (t.2 * quaternionHaarMono n (monoMul m (eσ t.1)) + phi n (rσ X) m).eqv
      (t.2 * quaternionHaarMono n (monoMul (eσ m) t.1) + phi n X (eσ m))
    exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _
      (term_reindex σ m t.1 hm (hX t List.mem_cons_self)))
      (phi_reindex m hm X fun s hs => hX s (List.mem_cons_of_mem _ hs))

/-- **Supported `PECongr` for block reindexing (PROVED).** -/
theorem pe_reindex {X Y : RatPoly} (hX : Sup n X) (hY : Sup n Y) (h : PE n X Y) : PE n (rσ X) (rσ Y) :=
  fun m => by
    cases hm : allZero (m.drop (4 * n))
    · exact Q'.eqv_trans _ _ _ (phi_null m hm _) (Q'.eqv_symm (phi_null m hm _))
    · exact Q'.eqv_trans _ _ _ (phi_reindex σ m hm X hX)
        (Q'.eqv_trans _ _ _ (h _) (Q'.eqv_symm (phi_reindex σ m hm Y hY)))

theorem sup_reindex (X : RatPoly) : Sup n (rσ X) := fun s hs => by
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hs
  exact Nat.le_of_eq (reindexQuaternionExponents_length σ t.1)

/-- The identity involution on one block. -/
def idInv : QuaternionBlockInvolution 1 := ⟨id, fun _ h => h, fun _ _ => rfl⟩

/-- **Unsupported `PECongr` fails (PROVED):** `x₄` (beyond the 4 coordinates of one block) is
Haar-context-null, but reindexing truncates it to the constant monomial. -/
theorem pecongr_fails :
    PE 1 [([0, 0, 0, 0, 1], (1 : Q'))] [] ∧
      ¬ PE 1 (reindexQuaternionPolynomial idInv [([0, 0, 0, 0, 1], (1 : Q'))])
        (reindexQuaternionPolynomial idInv []) := by
  refine ⟨fun m => ?_, fun h => ?_⟩
  · show ((1 : Q') * quaternionHaarMono 1 (monoMul m [0, 0, 0, 0, 1]) + 0).eqv 0
    have : quaternionHaarMono 1 (monoMul m [0, 0, 0, 0, 1]) = 0 := by
      unfold quaternionHaarMono
      cases hz : allZero ((monoMul m [0, 0, 0, 0, 1]).drop (4 * 1))
      · rfl
      · have := (allZero_iff _).mp hz 0
        rw [exponentAt_drop, exponentAt_monoMul] at this
        simp [exponentAt] at this
    rw [this]; decide
  · have := h []
    revert this; decide

end YMGap.Continuum.SU2ReindexPECongr
