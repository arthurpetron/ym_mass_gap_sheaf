import YMGap.Constructive.CRealSum
import YMGap.Constructive.CRealLe
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.RationalTail
import YMGap.Constructive.RationalsMul

/-!
# Reusable Tonelli factorization for nested character sums

The multi-index "Tonelli" step of the SU(N) cap — `Z_t(R) ≤ ∏_i S_i` — is, once
the per-axis factors are constructed (`CharacterTailMajorant.axisFactor`,
`PerAxisTail.axisFactor_geom_le`), NOT a measure-theoretic statement: it is a
bound on a NESTED FINITE `CReal.csum` whose term obeys a SEPARABLE rational
bound `term(λ) ≤ ∏_i aᵢ(λᵢ)`.  `SU3CharFactor.Z2D_le` is the rank-2 instance,
proved SU(3)-specifically against `charTerm2D`/`gBound`.

This module abstracts that proof off the SU(3) specifics into reusable Tonelli
lemmas at rank 2 (`csum2_prod_le`) and rank 3 (`csum3_prod_le`, the SU(4) case),
parameterized by an arbitrary term family and separable bound sequences.  Each
is exactly the nested-`leRat_csum` + `finSum` distributivity argument of
`Z2D_le`, with the outer/inner lengths independent.

Axiom-clean: only `propext`/`Quot.sound` (the substrate lemmas it composes).
-/

namespace YMGap.RG

open YMGap.Constructive

/-- Product-reorder `(x·y)·z ≃ (x·z)·y` (needed to thread the outer factor `x`
through the middle layer of the rank-3 nest). -/
theorem mul_swap_right_eqv (x y z : Q') :
    Q'.eqv ((x * y) * z) ((x * z) * y) := by
  -- (x·y)·z ≃ x·(y·z) ≃ x·(z·y) ≃ (x·z)·y
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv x y z) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left x (y * z) (z * y) (Q'.mul_comm_eqv y z)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv x z y)

/-- **Rank-2 Tonelli (reusable).**  A nested double `csum` whose term obeys a
separable rational bound `term p q ≤ a p · b q` is bounded by the product of the
two `finSum`s — `Z2D_le` with the SU(3) specifics abstracted away and the two
lengths `M`, `N` independent. -/
theorem csum2_prod_le (term : Nat → Nat → CReal) (a b : Nat → Q')
    (hterm : ∀ p q, CReal.leRat (term p q) (a p * b q)) (M N : Nat) :
    CReal.leRat
      (CReal.csum (fun p => CReal.csum (fun q => term p q) N) M)
      (RationalTail.finSum a M * RationalTail.finSum b N) := by
  -- inner row: Σ_q term p q ≤ a p · Σ_q b q
  have row : ∀ p, CReal.leRat (CReal.csum (fun q => term p q) N)
      (a p * RationalTail.finSum b N) := fun p =>
    CReal.leRat_mono
      (CReal.leRat_csum (fun q => term p q) (fun q => a p * b q) (hterm p) N)
      (Q'.le_of_eqv (Q'.eqv_symm (RationalTail.const_mul_finSum b (a p) N)))
  -- outer: Σ_p (a p · Σ b) ≤ (Σ a)·(Σ b)
  exact CReal.leRat_mono
    (CReal.leRat_csum (fun p => CReal.csum (fun q => term p q) N)
      (fun p => a p * RationalTail.finSum b N) row M)
    (Q'.le_of_eqv (Q'.eqv_symm
      (RationalTail.finSum_mul_const a (RationalTail.finSum b N) M)))

/-- **Rank-3 Tonelli (the SU(4) case).**  A triply-nested `csum` whose term
obeys the separable bound `term p q r ≤ (a p · b q) · c r` is bounded by the
product of three `finSum`s.  Same nested-`leRat_csum` argument, one layer
deeper; the middle layer uses `mul_swap_right_eqv` to thread the outer `a p`
factor past the `Σc` constant. -/
theorem csum3_prod_le (term : Nat → Nat → Nat → CReal) (a b c : Nat → Q')
    (hterm : ∀ p q r, CReal.leRat (term p q r) ((a p * b q) * c r))
    (M N L : Nat) :
    CReal.leRat
      (CReal.csum (fun p =>
        CReal.csum (fun q => CReal.csum (fun r => term p q r) L) N) M)
      ((RationalTail.finSum a M * RationalTail.finSum b N)
        * RationalTail.finSum c L) := by
  -- inner row (fixed p,q): Σ_r term p q r ≤ (a p · b q) · Σc
  have inner : ∀ p q, CReal.leRat (CReal.csum (fun r => term p q r) L)
      ((a p * b q) * RationalTail.finSum c L) := fun p q =>
    CReal.leRat_mono
      (CReal.leRat_csum (fun r => term p q r) (fun r => (a p * b q) * c r)
        (hterm p q) L)
      (Q'.le_of_eqv (Q'.eqv_symm (RationalTail.const_mul_finSum c (a p * b q) L)))
  -- re-shape the inner bound to (a p · Σc) · b q so the middle layer factors
  have inner' : ∀ p q, CReal.leRat (CReal.csum (fun r => term p q r) L)
      ((a p * RationalTail.finSum c L) * b q) := fun p q =>
    CReal.leRat_mono (inner p q)
      (Q'.le_of_eqv (mul_swap_right_eqv (a p) (b q) (RationalTail.finSum c L)))
  -- middle (fixed p): Σ_q (a p · Σc)·b q ≤ (a p · Σc) · Σb
  have mid : ∀ p, CReal.leRat
      (CReal.csum (fun q => CReal.csum (fun r => term p q r) L) N)
      ((a p * RationalTail.finSum c L) * RationalTail.finSum b N) := fun p =>
    CReal.leRat_mono
      (CReal.leRat_csum (fun q => CReal.csum (fun r => term p q r) L)
        (fun q => (a p * RationalTail.finSum c L) * b q) (inner' p) N)
      (Q'.le_of_eqv (Q'.eqv_symm
        (RationalTail.const_mul_finSum b (a p * RationalTail.finSum c L) N)))
  -- re-shape the middle bound to (a p · Σb) · Σc so the outer layer factors
  have mid' : ∀ p, CReal.leRat
      (CReal.csum (fun q => CReal.csum (fun r => term p q r) L) N)
      ((a p * RationalTail.finSum b N) * RationalTail.finSum c L) := fun p =>
    CReal.leRat_mono (mid p)
      (Q'.le_of_eqv (mul_swap_right_eqv (a p) (RationalTail.finSum c L)
        (RationalTail.finSum b N)))
  -- outer: Σ_p (a p · Σb)·Σc ≤ (Σa · Σb)·Σc
  refine CReal.leRat_mono
    (CReal.leRat_csum (fun p =>
        CReal.csum (fun q => CReal.csum (fun r => term p q r) L) N)
      (fun p => (a p * RationalTail.finSum b N) * RationalTail.finSum c L) mid' M) ?_
  -- goal: Σ_p ((a p·Σb)·Σc) ≤ (Σa · Σb)·Σc.  Show RHS ≃ LHS, then le_of_eqv∘symm.
  refine Q'.le_of_eqv (Q'.eqv_symm ?_)
  -- (Σa·Σb)·Σc ≃ (Σ_p a p·Σb)·Σc ≃ Σ_p ((a p·Σb)·Σc)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (RationalTail.finSum a M * RationalTail.finSum b N)
      (RationalTail.finSum (fun p => a p * RationalTail.finSum b N) M)
      (RationalTail.finSum c L)
      (RationalTail.finSum_mul_const a (RationalTail.finSum b N) M)) ?_
  exact RationalTail.finSum_mul_const
    (fun p => a p * RationalTail.finSum b N) (RationalTail.finSum c L) M

/-- Two-sided product monotonicity: `x ≤ X`, `y ≤ Y`, `0 ≤ y`, `0 ≤ X` ⟹
`x·y ≤ X·Y`.  (Mathlib-free; chains the two one-sided `mul_le_mul` lemmas.) -/
theorem mul_le_mul_both (x y X Y : Q') (hx : x ≤ X) (hy : y ≤ Y)
    (h0y : (0 : Q') ≤ y) (h0X : (0 : Q') ≤ X) : x * y ≤ X * Y :=
  Q'.le_trans' (x * y) (X * y) (X * Y)
    (Q'.mul_le_mul_of_nonneg_right x X y hx h0y)
    (Q'.mul_le_mul_of_nonneg_left y Y X hy h0X)

/-- A `finSum` of a nonnegative sequence is nonnegative. -/
theorem finSum_nonneg (f : Nat → Q') (h0 : ∀ m, (0 : Q') ≤ f m) (n : Nat) :
    (0 : Q') ≤ RationalTail.finSum f n :=
  RationalTail.finSum_monotone_of_nonneg f h0 0 n (Nat.zero_le n)

/-- **Rank-3 cap (the SU(4) capstone shape).**  Composes the rank-3 Tonelli
(`csum3_prod_le`) with three per-axis geometric closures `finSum aᵢ ≤ Hᵢ` to bound
the full triply-nested character sum by the constant rational product
`(Ha·Hb)·Hc`, for ALL truncation lengths.

This leaves exactly two named inputs: (1) `hterm`, the SEPARABLE analytic bound
`term λ ≤ ∏ᵢ aᵢ(λᵢ)` (Casimir split `C₂(λ) ≥ Σ hᵢ(λᵢ)` + Weyl-dim factorization,
each `e^{−t·}` dominated by a rational `ρ^{λᵢ}`); (2) `hA/hB/hC`, the per-axis
geometric closures (discharged by `CharacterTail.geom_series_le` for the concrete
SU(4) ρᵢ, qᵢ = 3,4,3).  The multi-index combinatorics is now internal. -/
theorem csum3_cap (term : Nat → Nat → Nat → CReal) (a b c : Nat → Q')
    (Ha Hb Hc : Q')
    (hterm : ∀ p q r, CReal.leRat (term p q r) ((a p * b q) * c r))
    (ha0 : ∀ m, (0 : Q') ≤ a m) (hb0 : ∀ m, (0 : Q') ≤ b m)
    (hc0 : ∀ m, (0 : Q') ≤ c m)
    (hHa : (0 : Q') ≤ Ha) (hHb : (0 : Q') ≤ Hb)
    (hA : ∀ M, RationalTail.finSum a M ≤ Ha)
    (hB : ∀ N, RationalTail.finSum b N ≤ Hb)
    (hC : ∀ L, RationalTail.finSum c L ≤ Hc)
    (M N L : Nat) :
    CReal.leRat
      (CReal.csum (fun p =>
        CReal.csum (fun q => CReal.csum (fun r => term p q r) L) N) M)
      ((Ha * Hb) * Hc) := by
  refine CReal.leRat_mono (csum3_prod_le term a b c hterm M N L) ?_
  -- (Σa·Σb)·Σc ≤ (Ha·Hb)·Hc  via two-sided product monotonicity
  have hAB : RationalTail.finSum a M * RationalTail.finSum b N ≤ Ha * Hb :=
    mul_le_mul_both _ _ _ _ (hA M) (hB N) (finSum_nonneg b hb0 N) hHa
  exact mul_le_mul_both _ _ _ _ hAB (hC L) (finSum_nonneg c hc0 L)
    (Q'.mul_nonneg Ha Hb hHa hHb)

end YMGap.RG

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RG.mul_swap_right_eqv
#print axioms YMGap.RG.csum2_prod_le
#print axioms YMGap.RG.csum3_prod_le
#print axioms YMGap.RG.mul_le_mul_both
#print axioms YMGap.RG.finSum_nonneg
#print axioms YMGap.RG.csum3_cap
