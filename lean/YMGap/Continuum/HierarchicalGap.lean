/-
The FIRST unconditional positive-and-finite continuum mass gap in this
development, on the EXACT heat-kernel DECIMATION LINE (δ = 0).

# What this module is — and what it is NOT (read first, honesty contract)

This module proves a GENUINE, DERIVED, UNCONDITIONAL two-sided continuum mass
gap — but on the EXACTLY-SOLUBLE heat-kernel DECIMATION LINE, the
dimensionally-reduced RG-fixed-point flow with the bond-moving residual `δ` set
to `0`.  It is the FIRST place in the development where a positive AND finite
continuum gap is obtained with NO hypotheses: `τ, a₀, b, c` are explicit positive
parameters of the model and the gap is computed from them.

It is **NOT** the 4D Yang–Mills mass gap.  The decimation line is the
heat-semigroup half of a Migdal–Kadanoff block step, where the separator
commutes with the heat semigroup EXACTLY (`sep_k = (sep_{k+1})^b`), so the orbit
is exactly soluble and dimension-agnostic (decimation does not see the spacetime
dimension `d`).  The genuine 4D content is the bond-moving residual `δ` (the
deviation between this exact decimation orbit and the physical gauge-invariant
separator), which is NOT addressed here and remains open.

So: the number below is a real dimensional-transmutation result for the
exactly-soluble model, not a solution of the Clay problem.  Every doc-section
restates this limitation.

# The construction (the math formalized here)

Heat-kernel-time decimation flow toward the continuum:

  * heat-kernel time   `t_k = τ / bᵏ`            (`τ > 0`, integer `b ≥ 2`);
  * the exponent        `y_k = c·τ / bᵏ`          (a positive rational, `c > 0`;
    physically `c = 3` since `sep = w³ = e^{−3t/4}`, constants absorbed);
  * the separator       `sep_k = e^{−y_k}`        (a `CReal`), with the EXACT
    decimation relation `y_k = b · y_{k+1}` (`decimation_exponent`), hence
    `sep_k ≃ e^{−(b · y_{k+1})}` (`decimation_step`) — this is what makes the
    orbit a genuine RG decimation orbit, not an arbitrary choice;
  * the spacing         `a_k = a₀ / bᵏ`           (`a₀ > 0`), `→ 0`;
  * the physical margin `margin_k = 1 − e^{−y_k}` (a `CReal`);
  * the physical gap    `physGap_k = margin_k · (bᵏ / a₀) = margin_k / a_k`.

# The two-sided bound (the crux)

  * LOWER  `1 − e^{−y} ≥ y/2` for `0 ≤ y ≤ 1`  — reused from
    `BareAFDiagnostic.oneSubExpNeg_ge_half` (stated as `e^{−y} ≤ 1 − y/2`).
  * UPPER  `1 − e^{−y} ≤ y` for `y ≥ 0`  — equivalently `e^{−y} ≥ 1 − y`, proved
    here as `expNeg_geRat_oneSubArg` from the alternating series: every partial
    sum `partialSum y n ≥ 1 − y` (`partialSum_ge_oneSub`), via the pair-sum
    nonnegativity of the magnitude-decreasing alternating terms (`0 ≤ y ≤ 1`).

With `y_k = c·τ/bᵏ`, `margin_k ∈ [y_k/2, y_k] = [cτ/(2bᵏ), cτ/bᵏ]`, hence
`physGap_k = margin_k·bᵏ/a₀ ∈ [cτ/(2a₀), cτ/a₀]` for all `k ≥ k₀` (where
`y_{k₀} ≤ 1`); the UPPER bound holds for ALL `k`, the LOWER for `k ≥ k₀`.

# The headline (unconditional)

`hierarchical_physGapMin_pos` : `physGapMin = cτ/(2a₀) > 0` is a uniform LOWER
floor `geRat (physGap k) physGapMin` for all `k ≥ k₀`, with the finiteness
companion `physGapMax = cτ/a₀` an upper ceiling `leRat (physGap k) physGapMax`
for ALL `k`.  No hypotheses on the model — the bound is DERIVED.

The margins are `CReal`, so the order statements use the SOUND limit-order
predicates `ExpPos.geRat` (limit `≥` a rational) and `CReal.leRat` (limit `≤` a
rational), which is the CReal-correct form of the floor/ceiling.  The existing
`PhysicalSeparator.PhysicalGapFloor` bridge is `Q'.divPos`-based (rational
margins); feeding this CReal-margin gap into it would need a CReal-variant of
`PhysicalGapFloor` whose `floor`/`finiteness` fields are `geRat`/`leRat` on a
`CReal` separator margin.  That bridge is noted, not forced (see §6).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
All witnesses (`physGapMin`, `physGapMax`, the moduli) are `Type`-level `Q'` /
`CReal` data.
-/

import YMGap.Continuum.BareAFDiagnostic
import YMGap.Constructive.ExpNeg
import YMGap.Constructive.ExpPos
import YMGap.Constructive.CRealLe
import YMGap.Constructive.CRealAdd
import YMGap.Constructive.CRealMul
import YMGap.Constructive.CRealMulMono
import YMGap.Constructive.ExpNegCongr
import YMGap.Constructive.Sqrt
import YMGap.Constructive.Geometric
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.HierarchicalGap

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.ExpPos

/-- The constant `1/2 : Q'`, reused from `BareAFDiagnostic` so the `half` here
agrees definitionally with the one inside `oneSubExpNeg_ge_half`. -/
abbrev half : Q' := BareAFDiagnostic.half

/-! ## 0. Pure-`Q'` substrate: term parity and decrease of the `e^{−y}` series

For `0 ≤ y ≤ 1` the magnitude terms decrease (`termAbs_antitone_step`) and the
signed terms alternate (`term_parity`).  Together the consecutive PAIRS are
nonnegative (`term_pair_nonneg`) and the even-index terms are nonnegative
(`term_even_nonneg`), which is exactly what makes every partial sum
`≥ 1 − y` — the UPPER margin bound. -/

/-- The ratio factor `y · invSucc k = y/(k+1) ≤ 1` for `0 ≤ y ≤ 1` (since
`y ≤ 1 ≤ k+1`). -/
theorem y_invSucc_le_one (y : Q') (hy0 : (0 : Q') ≤ y) (hy1 : y ≤ 1) (k : Nat) :
    y * Q'.invSucc k ≤ 1 := by
  -- y · invSucc k ≤ 1 · invSucc k ≤ 1 · 1 = 1? No: invSucc k ≤ 1, y ≤ 1.
  -- y·invSucc k ≤ 1·invSucc k = invSucc k ≤ invSucc 0 = 1.
  have h1 : y * Q'.invSucc k ≤ (1 : Q') * Q'.invSucc k :=
    Q'.mul_le_mul_of_nonneg_right y 1 (Q'.invSucc k) hy1 (Q'.invSucc_nonneg k)
  have h2 : (1 : Q') * Q'.invSucc k ≤ Q'.invSucc k :=
    Q'.le_of_eqv (Q'.one_mul_eqv (Q'.invSucc k))
  have h3 : Q'.invSucc k ≤ Q'.invSucc 0 := invSucc_le_of_le (Nat.zero_le k)
  have h4 : Q'.invSucc 0 ≤ (1 : Q') := by decide
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 (Q'.le_trans' _ _ _ h3 h4))

/-- **Magnitude terms decrease** for `0 ≤ y ≤ 1`:
`termAbs y (k+1) ≤ termAbs y k`.  One step multiplies by `y · invSucc k ≤ 1`. -/
theorem termAbs_antitone_step (y : Q') (hy0 : (0 : Q') ≤ y) (hy1 : y ≤ 1) (k : Nat) :
    termAbs y (k + 1) ≤ termAbs y k := by
  show termAbs y k * (y * Q'.invSucc k) ≤ termAbs y k
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left (y * Q'.invSucc k) 1 (termAbs y k)
      (y_invSucc_le_one y hy0 hy1 k) (termAbs_nonneg y hy0 k)) ?_
  exact Q'.le_of_eqv (Q'.mul_one_eqv (termAbs y k))

/-- **Term parity.**  `term y (2k) ≃ termAbs y (2k)` and
`term y (2k+1) ≃ −(termAbs y (2k+1))`: the signed terms are the magnitudes with
alternating sign.  Proved by induction on `k`, threading the recurrence factor
`(−y)·invSucc` against `y·invSucc`. -/
theorem term_parity (y : Q') :
    ∀ k, (term y (2 * k)).eqv (termAbs y (2 * k)) ∧
      (term y (2 * k + 1)).eqv (-(termAbs y (2 * k + 1)))
  | 0 => by
    refine ⟨?_, ?_⟩
    · show (term y 0).eqv (termAbs y 0); exact Q'.eqv_refl _
    · -- term y 1 = 1·((−y)·invSucc 0) ; termAbs y 1 = 1·(y·invSucc 0)
      show (term y 1).eqv (-(termAbs y 1))
      show ((1 : Q') * ((-y) * Q'.invSucc 0)).eqv (-((1 : Q') * (y * Q'.invSucc 0)))
      refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv ((-y) * Q'.invSucc 0)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv y (Q'.invSucc 0)) ?_
      exact Q'.neg_eqv_congr _ _ (Q'.eqv_symm (Q'.one_mul_eqv (y * Q'.invSucc 0)))
  | k + 1 => by
    obtain ⟨ihEven, ihOdd⟩ := term_parity y k
    -- 2(k+1) = (2k+1)+1 ; 2(k+1)+1 = (2k+2)+1
    have he : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    have ho : 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 := rfl
    refine ⟨?_, ?_⟩
    · -- term y (2(k+1)) = term y (2k+1) · ((−y)·c) ≃ −termAbs(2k+1) · ((−y)·c)
      --                  ≃ termAbs(2k+1) · (y·c) = termAbs y (2(k+1))
      rw [he]
      show (term y (2 * k + 1) * ((-y) * Q'.invSucc (2 * k + 1))).eqv
        (termAbs y ((2 * k + 1) + 1))
      show (term y (2 * k + 1) * ((-y) * Q'.invSucc (2 * k + 1))).eqv
        (termAbs y (2 * k + 1) * (y * Q'.invSucc (2 * k + 1)))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ ((-y) * Q'.invSucc (2 * k + 1)) ihOdd) ?_
      -- (−termAbs)·((−y)·c) ≃ termAbs·(y·c)
      refine Q'.eqv_trans _ _ _
        (Q'.neg_mul_eqv (termAbs y (2 * k + 1)) ((-y) * Q'.invSucc (2 * k + 1))) ?_
      -- −(termAbs·((−y)·c)) ≃ termAbs·(−((−y)·c)) ≃ termAbs·(y·c)
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_neg_eqv (termAbs y (2 * k + 1)) ((-y) * Q'.invSucc (2 * k + 1)))) ?_
      refine Q'.mul_eqv_congr_left (termAbs y (2 * k + 1)) _ _ ?_
      -- −((−y)·c) ≃ (−(−y))·c ≃ y·c
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.neg_mul_eqv (-y) (Q'.invSucc (2 * k + 1)))) ?_
      exact Q'.mul_eqv_congr_right _ _ (Q'.invSucc (2 * k + 1)) (Q'.neg_neg_eqv y)
    · -- term y (2(k+1)+1) = term y (2(k+1)) · ((−y)·c) ≃ termAbs(2(k+1))·((−y)·c)
      --                    ≃ −(termAbs(2(k+1))·(y·c)) = −termAbs y (2(k+1)+1)
      have hEven' : (term y (2 * (k + 1))).eqv (termAbs y (2 * (k + 1))) := by
        rw [he]
        -- reuse the even half just proved
        show (term y ((2 * k + 1) + 1)).eqv (termAbs y ((2 * k + 1) + 1))
        show (term y (2 * k + 1) * ((-y) * Q'.invSucc (2 * k + 1))).eqv
          (termAbs y (2 * k + 1) * (y * Q'.invSucc (2 * k + 1)))
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ ((-y) * Q'.invSucc (2 * k + 1)) ihOdd) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.neg_mul_eqv (termAbs y (2 * k + 1)) ((-y) * Q'.invSucc (2 * k + 1))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_neg_eqv (termAbs y (2 * k + 1)) ((-y) * Q'.invSucc (2 * k + 1)))) ?_
        refine Q'.mul_eqv_congr_left (termAbs y (2 * k + 1)) _ _ ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.neg_mul_eqv (-y) (Q'.invSucc (2 * k + 1)))) ?_
        exact Q'.mul_eqv_congr_right _ _ (Q'.invSucc (2 * k + 1)) (Q'.neg_neg_eqv y)
      show (term y ((2 * (k + 1)) + 1)).eqv (-(termAbs y ((2 * (k + 1)) + 1)))
      show (term y (2 * (k + 1)) * ((-y) * Q'.invSucc (2 * (k + 1)))).eqv
        (-(termAbs y (2 * (k + 1)) * (y * Q'.invSucc (2 * (k + 1)))))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ ((-y) * Q'.invSucc (2 * (k + 1))) hEven') ?_
      -- termAbs·((−y)·c) ≃ termAbs·(−(y·c)) ≃ −(termAbs·(y·c))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (termAbs y (2 * (k + 1))) _ _
          (Q'.neg_mul_eqv y (Q'.invSucc (2 * (k + 1))))) ?_
      exact Q'.mul_neg_eqv (termAbs y (2 * (k + 1))) (y * Q'.invSucc (2 * (k + 1)))

/-- The even-index signed term is nonnegative for `0 ≤ y`. -/
theorem term_even_nonneg (y : Q') (hy0 : (0 : Q') ≤ y) (k : Nat) :
    (0 : Q') ≤ term y (2 * k) :=
  Q'.le_trans' _ _ _ (termAbs_nonneg y hy0 (2 * k))
    (Q'.ge_of_eqv (term_parity y k).1)

/-- **Consecutive pairs are nonnegative**: `0 ≤ term y (2k) + term y (2k+1)` for
`0 ≤ y ≤ 1`.  The pair equals `termAbs y (2k) − termAbs y (2k+1) ≥ 0` because the
magnitudes decrease (`termAbs_antitone_step`). -/
theorem term_pair_nonneg (y : Q') (hy0 : (0 : Q') ≤ y) (hy1 : y ≤ 1) (k : Nat) :
    (0 : Q') ≤ term y (2 * k) + term y (2 * k + 1) := by
  obtain ⟨hEven, hOdd⟩ := term_parity y k
  -- term y (2k) + term y (2k+1) ≥ termAbs(2k) + (−termAbs(2k+1)) ≥ 0
  have hdec : termAbs y (2 * k + 1) ≤ termAbs y (2 * k) :=
    termAbs_antitone_step y hy0 hy1 (2 * k)
  -- 0 ≤ termAbs(2k) + (−termAbs(2k+1))
  have hbase : (0 : Q') ≤ termAbs y (2 * k) + (-(termAbs y (2 * k + 1))) := by
    -- termAbs(2k+1) ≤ termAbs(2k)  ⟹  0 ≤ termAbs(2k) − termAbs(2k+1)
    have h1 : termAbs y (2 * k + 1) + (-(termAbs y (2 * k + 1)))
        ≤ termAbs y (2 * k) + (-(termAbs y (2 * k + 1))) :=
      Q'.add_le_add_right _ _ (-(termAbs y (2 * k + 1))) hdec
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv (termAbs y (2 * k + 1)))) h1
  -- transport along the parity equivalences
  refine Q'.le_trans' _ _ _ hbase (Q'.le_of_eqv ?_)
  refine Q'.eqv_symm ?_
  -- term(2k) + term(2k+1) ≃ termAbs(2k) + term(2k+1) ≃ termAbs(2k) + (−termAbs(2k+1))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (term y (2 * k)) (termAbs y (2 * k)) (term y (2 * k + 1)) hEven) ?_
  exact Q'.add_eqv_congr_left (termAbs y (2 * k)) (term y (2 * k + 1))
    (-(termAbs y (2 * k + 1))) hOdd

/-! ## 1. Every partial sum is `≥ 1 − y` (the UPPER margin bound)

For `0 ≤ y ≤ 1`, the alternating-series partial sums never dip below `1 − y`:
`partialSum y n ≥ 1 + (−y)` for `n ≥ 1`.  Proved by induction over the index in
steps of two, using `term_pair_nonneg` (an even-started pair never decreases the
sum below the previous even value) and `term_even_nonneg` (the trailing single
term at an even index only adds). -/

/-- The two-index simultaneous invariant: from index `2`, both even and odd
partial sums stay `≥ 1 + (−y)`. -/
theorem partialSum_ge_oneSub_aux (y : Q') (hy0 : (0 : Q') ≤ y) (hy1 : y ≤ 1) :
    ∀ k, (1 + (-y)) ≤ partialSum y (2 + 2 * k) ∧
      (1 + (-y)) ≤ partialSum y (3 + 2 * k)
  | 0 => by
    refine ⟨?_, ?_⟩
    · -- partialSum y 2 = 1 + term y 1 ; term y 1 ≃ −y
      have h2 : partialSum y 2 = 1 + term y 1 := partialSum_two y
      have ht1 : (term y 1).eqv (-y) := by
        -- term y 1 = (term y 0)·((−y)·invSucc 0) = 1·((−y)·c)
        show ((1 : Q') * ((-y) * Q'.invSucc 0)).eqv (-y)
        refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv ((-y) * Q'.invSucc 0)) ?_
        -- (−y)·invSucc 0 ≃ −y  (invSucc 0 = 1)
        refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (-y) (Q'.invSucc 0) 1 ?_) ?_
        · show (Q'.invSucc 0).eqv 1; decide
        · exact Q'.mul_one_eqv (-y)
      rw [h2]
      exact Q'.le_of_eqv (Q'.add_eqv_congr_left 1 (-y) (term y 1) (Q'.eqv_symm ht1))
    · -- partialSum y 3 = partialSum y 2 + term y 2 ≥ partialSum y 2 ≥ 1 + (−y)
      have hbase : (1 + (-y)) ≤ partialSum y 2 := by
        have h2 : partialSum y 2 = 1 + term y 1 := partialSum_two y
        have ht1 : (term y 1).eqv (-y) := by
          show ((1 : Q') * ((-y) * Q'.invSucc 0)).eqv (-y)
          refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv ((-y) * Q'.invSucc 0)) ?_
          refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (-y) (Q'.invSucc 0) 1 ?_) ?_
          · show (Q'.invSucc 0).eqv 1; decide
          · exact Q'.mul_one_eqv (-y)
        rw [h2]
        exact Q'.le_of_eqv (Q'.add_eqv_congr_left 1 (-y) (term y 1) (Q'.eqv_symm ht1))
      -- partialSum y 3 = partialSum y 2 + term y 2 ; term y 2 = term y (2·1) ≥ 0
      have h3 : partialSum y 3 = partialSum y 2 + term y 2 := rfl
      have hte : (0 : Q') ≤ term y 2 := by
        have := term_even_nonneg y hy0 1; simpa using this
      rw [h3]
      exact Q'.le_trans' _ _ _ hbase (Q'.add_le_self_of_nonneg (partialSum y 2) (term y 2) hte)
  | k + 1 => by
    obtain ⟨ihEven, ihOdd⟩ := partialSum_ge_oneSub_aux y hy0 hy1 k
    -- 2 + 2(k+1) = (2 + 2k) + 2 ; the added pair starts at even index (2 + 2k)
    have hidxE : 2 + 2 * (k + 1) = ((2 + 2 * k) + 1) + 1 := by omega
    have hidxO : 3 + 2 * (k + 1) = (((2 + 2 * k) + 1) + 1) + 1 := by omega
    refine ⟨?_, ?_⟩
    · -- partialSum y (2+2(k+1)) = partialSum y (2+2k) + (term(2+2k) + term(2+2k+1))
      rw [hidxE]
      show (1 + (-y)) ≤ partialSum y ((2 + 2 * k) + 1) + term y ((2 + 2 * k) + 1)
      -- = (partialSum y (2+2k) + term y (2+2k)) + term y (2+2k+1)
      -- the pair term y (2+2k) + term y (2+2k+1) ≥ 0 ; index 2+2k = 2·(k+1) is even
      have hpair : (0 : Q') ≤ term y (2 + 2 * k) + term y (2 + 2 * k + 1) := by
        have hev : 2 + 2 * k = 2 * (k + 1) := by omega
        rw [hev]
        exact term_pair_nonneg y hy0 hy1 (k + 1)
      have hstep : partialSum y (2 + 2 * k)
          ≤ (partialSum y (2 + 2 * k) + term y (2 + 2 * k)) + term y (2 + 2 * k + 1) := by
        refine Q'.le_trans' _ _ _
          (Q'.add_le_self_of_nonneg (partialSum y (2 + 2 * k))
            (term y (2 + 2 * k) + term y (2 + 2 * k + 1)) hpair) ?_
        exact Q'.le_of_eqv (Q'.eqv_symm (Q'.add_assoc_eqv (partialSum y (2 + 2 * k))
          (term y (2 + 2 * k)) (term y (2 + 2 * k + 1))))
      -- rewrite the goal's partialSum ((2+2k)+1) = partialSum y (2+2k) + term y (2+2k)
      have hps : partialSum y ((2 + 2 * k) + 1) = partialSum y (2 + 2 * k) + term y (2 + 2 * k) :=
        rfl
      rw [hps]
      exact Q'.le_trans' _ _ _ ihEven hstep
    · -- partialSum y (3+2(k+1)) = partialSum y (2+2(k+1)) + term y (2+2(k+1)); even ⟹ ≥
      rw [hidxO]
      show (1 + (-y)) ≤ partialSum y (((2 + 2 * k) + 1) + 1) + term y (((2 + 2 * k) + 1) + 1)
      -- the even partial sum at index 2+2(k+1) is ≥ 1+(−y) (just proved), add nonneg even term
      have hEvenNext : (1 + (-y)) ≤ partialSum y (((2 + 2 * k) + 1) + 1) := by
        -- this is the even half at k+1, which we re-establish inline to avoid mutual recursion
        have hpair : (0 : Q') ≤ term y (2 + 2 * k) + term y (2 + 2 * k + 1) := by
          have hev : 2 + 2 * k = 2 * (k + 1) := by omega
          rw [hev]; exact term_pair_nonneg y hy0 hy1 (k + 1)
        have hps : partialSum y ((2 + 2 * k) + 1)
            = partialSum y (2 + 2 * k) + term y (2 + 2 * k) := rfl
        have hps2 : partialSum y (((2 + 2 * k) + 1) + 1)
            = (partialSum y (2 + 2 * k) + term y (2 + 2 * k)) + term y ((2 + 2 * k) + 1) := by
          rw [show (((2 + 2 * k) + 1) + 1) = ((2 + 2 * k) + 1) + 1 from rfl]
          show partialSum y ((2 + 2 * k) + 1) + term y ((2 + 2 * k) + 1)
              = (partialSum y (2 + 2 * k) + term y (2 + 2 * k)) + term y ((2 + 2 * k) + 1)
          rw [hps]
        have hstep : partialSum y (2 + 2 * k)
            ≤ (partialSum y (2 + 2 * k) + term y (2 + 2 * k)) + term y ((2 + 2 * k) + 1) := by
          refine Q'.le_trans' _ _ _
            (Q'.add_le_self_of_nonneg (partialSum y (2 + 2 * k))
              (term y (2 + 2 * k) + term y (2 + 2 * k + 1)) hpair) ?_
          exact Q'.le_of_eqv (Q'.eqv_symm (Q'.add_assoc_eqv (partialSum y (2 + 2 * k))
            (term y (2 + 2 * k)) (term y (2 + 2 * k + 1))))
        rw [hps2]
        exact Q'.le_trans' _ _ _ ihEven hstep
      -- term y (2+2(k+1)) : index ((2+2k)+1)+1 = 2·(k+2) is even ⟹ ≥ 0
      have hteNonneg : (0 : Q') ≤ term y (((2 + 2 * k) + 1) + 1) := by
        have hev : ((2 + 2 * k) + 1) + 1 = 2 * (k + 2) := by omega
        rw [hev]; exact term_even_nonneg y hy0 (k + 2)
      exact Q'.le_trans' _ _ _ hEvenNext
        (Q'.add_le_self_of_nonneg _ _ hteNonneg)

/-- **Every partial sum is `≥ 1 − y`** (for `n ≥ 2`, `0 ≤ y ≤ 1`):
`1 + (−y) ≤ partialSum y n`.  Splitting `n = 2 + 2k` (even) or `n = 3 + 2k` (odd)
and applying the two-index invariant. -/
theorem partialSum_ge_oneSub (y : Q') (hy0 : (0 : Q') ≤ y) (hy1 : y ≤ 1)
    (n : Nat) (hn : 2 ≤ n) : (1 + (-y)) ≤ partialSum y n := by
  -- n = 2 + m ; case on parity of m via m % 2.
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn   -- n = 2 + m
  rcases Nat.lt_or_ge (m % 2) 1 with hmod | hmod
  · -- m even: m = 2·(m/2)
    have : 2 + m = 2 + 2 * (m / 2) := by omega
    rw [this]
    exact (partialSum_ge_oneSub_aux y hy0 hy1 (m / 2)).1
  · -- m odd: m = 2·(m/2)+1 ⟹ n = 3 + 2·(m/2)
    have : 2 + m = 3 + 2 * (m / 2) := by omega
    rw [this]
    exact (partialSum_ge_oneSub_aux y hy0 hy1 (m / 2)).2

/-- **`e^{−y} ≥ 1 − y` for `0 ≤ y ≤ 1`** — the UPPER margin bound, as a `geRat`
lower bound on `expNeg`.  Every partial sum from index `2` is `≥ 1 + (−y)`, so
the limit is too. -/
theorem expNeg_geRat_oneSubArg (y : Q') (hy0 : (0 : Q') ≤ y) (hy1 : y ≤ 1) :
    ExpPos.geRat (ExpNeg.expNeg y hy0) (1 + (-y)) :=
  ExpPos.geRat_of_eventually
    ⟨2, fun n hn => partialSum_ge_oneSub y hy0 hy1 n hn⟩

/-! ## 2. Margin bounds — lifting the scalar exp inequalities to the `CReal` margin

`marginCReal y = 1 − e^{−y}` (a `CReal`).  Its lower bound `geRat ≥ y/2` comes
from `oneSubExpNeg_ge_half` (`e^{−y} ≤ 1 − y/2`); its upper bound `leRat ≤ y`
comes from `expNeg_geRat_oneSubArg` (`e^{−y} ≥ 1 − y`).  Both are obtained by
turning a bound on `e^{−y}` into the dual bound on `1 − e^{−y}`. -/

/-- The physical margin as a `CReal`: `marginCReal y = 1 + (−e^{−y})`. -/
def marginCReal (y : Q') (hy : (0 : Q') ≤ y) : CReal :=
  CReal.add (CReal.ofQ' 1) (CReal.neg (ExpNeg.expNeg y hy))

/-- `geRat (neg E) (−b)` from `leRat E b`: negation flips a sound upper bound to a
sound lower bound on the negation. -/
theorem geRat_neg_of_leRat {E : CReal} {b : Q'} (h : CReal.leRat E b) :
    ExpPos.geRat (CReal.neg E) (-b) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  -- want: −b ≤ (neg E).approx n + ε = −(E.approx n) + ε
  show (-b) ≤ (-(E.approx n)) + ε
  exact Q'.neg_le_neg_add' (hN n hn)

/-- `leRat (neg E) (−b)` from `geRat E b`: negation flips a sound lower bound to a
sound upper bound on the negation. -/
theorem leRat_neg_of_geRat {E : CReal} {b : Q'} (h : ExpPos.geRat E b) :
    CReal.leRat (CReal.neg E) (-b) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  show (-(E.approx n)) ≤ (-b) + ε
  exact Q'.neg_le_neg_add' (hN n hn)

/-- `geRat` of a sum from `geRat` of the summands. -/
theorem geRat_add {x y : CReal} {a b : Q'}
    (hx : ExpPos.geRat x a) (hy : ExpPos.geRat y b) :
    ExpPos.geRat (CReal.add x y) (a + b) := by
  intro ε hε
  have hhε : (0 : Q') < half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Nx, hNx⟩ := hx (half * ε) hhε
  obtain ⟨Ny, hNy⟩ := hy (half * ε) hhε
  refine ⟨max Nx Ny, fun n hn => ?_⟩
  have hnx : Nx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hny : Ny ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have h1 := hNx n hnx
  have h2 := hNy n hny
  -- a + b ≤ (x_n + ½ε) + (y_n + ½ε) ≃ (x_n + y_n) + ε
  have hsum : a + b ≤ (x.approx n + half * ε) + (y.approx n + half * ε) :=
    Q'.add_le_add h1 h2
  show a + b ≤ (x.approx n + y.approx n) + ε
  refine Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _
    (Q'.regroup (x.approx n) (y.approx n) (half * ε)) ?_
  exact Q'.add_eqv_congr_left (x.approx n + y.approx n) (half * ε + half * ε) ε
    (ExpNeg.two_halves ε)

/-- **Margin LOWER bound** `marginCReal y ≥ y/2` for `0 ≤ y ≤ 1`.
From `e^{−y} ≤ 1 − y/2` (`oneSubExpNeg_ge_half`): `1 − e^{−y} ≥ 1 − (1 − y/2)
= y/2`.  Reported as `geRat (marginCReal y) (half * y)`. -/
theorem marginCReal_geRat_half (y : Q') (hy0 : (0 : Q') ≤ y) (hy1 : y ≤ 1) :
    ExpPos.geRat (marginCReal y hy0) (half * y) := by
  -- e^{−y} ≤ 1 + (−(half·y))
  have hub : CReal.leRat (ExpNeg.expNeg y hy0) (1 + (-(half * y))) :=
    BareAFDiagnostic.oneSubExpNeg_ge_half y hy0 hy1
  -- geRat (neg e^{−y}) (−(1 + (−(half·y))))
  have hneg : ExpPos.geRat (CReal.neg (ExpNeg.expNeg y hy0)) (-(1 + (-(half * y)))) :=
    geRat_neg_of_leRat hub
  -- geRat (1 + neg e^{−y}) (1 + (−(1 + (−(half·y)))))
  have hsum : ExpPos.geRat (marginCReal y hy0)
      ((1 : Q') + (-(1 + (-(half * y))))) := by
    have hone : ExpPos.geRat (CReal.ofQ' (1 : Q')) (1 : Q') :=
      ExpPos.geRat_of_eventually ⟨0, fun n _ => Q'.le_refl' _⟩
    exact geRat_add hone hneg
  -- 1 + (−(1 + (−(half·y)))) ≃ half·y
  refine ExpPos.geRat_mono hsum ?_
  -- half·y ≤ 1 + (−(1 + (−(half·y))))
  apply Q'.le_of_eqv
  -- half·y ≃ 1 + (−(1 + (−(half·y))))
  refine Q'.eqv_symm ?_
  -- 1 + (−(1 + (−(half·y)))) ≃ 1 + ((−1) + (half·y)) ≃ (1 + (−1)) + half·y ≃ half·y
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 (-(1 + (-(half * y)))) ((-1) + (half * y)) ?_) ?_
  · -- −(1 + (−(half·y))) ≃ (−1) + half·y
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv 1 (-(half * y))) ?_
    exact Q'.add_eqv_congr_left (-1) (-(-(half * y))) (half * y) (Q'.neg_neg_eqv (half * y))
  · -- 1 + ((−1) + half·y) ≃ (1 + (−1)) + half·y ≃ 0 + half·y ≃ half·y
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv 1 (-1) (half * y))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (1 + (-1)) 0 (half * y) (Q'.add_neg_self_eqv 1)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (half * y))

/-- **Margin UPPER bound** `marginCReal y ≤ y` for `0 ≤ y ≤ 1`.
From `e^{−y} ≥ 1 − y` (`expNeg_geRat_oneSubArg`): `1 − e^{−y} ≤ 1 − (1 − y) = y`.
Reported as `leRat (marginCReal y) y`. -/
theorem marginCReal_leRat (y : Q') (hy0 : (0 : Q') ≤ y) (hy1 : y ≤ 1) :
    CReal.leRat (marginCReal y hy0) y := by
  -- e^{−y} ≥ 1 + (−y)
  have hlb : ExpPos.geRat (ExpNeg.expNeg y hy0) (1 + (-y)) :=
    expNeg_geRat_oneSubArg y hy0 hy1
  -- leRat (neg e^{−y}) (−(1 + (−y)))
  have hneg : CReal.leRat (CReal.neg (ExpNeg.expNeg y hy0)) (-(1 + (-y))) :=
    leRat_neg_of_geRat hlb
  -- leRat (1 + neg e^{−y}) (1 + (−(1 + (−y))))
  have hsum : CReal.leRat (marginCReal y hy0) ((1 : Q') + (-(1 + (-y)))) :=
    CReal.leRat_add (CReal.leRat_ofQ' (Q'.le_refl' 1)) hneg
  refine CReal.leRat_mono hsum ?_
  -- 1 + (−(1 + (−y))) ≃ y  ⟹  ≤ y
  apply Q'.le_of_eqv
  -- 1 + (−(1 + (−y))) ≃ 1 + ((−1) + y) ≃ (1+(−1)) + y ≃ y
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 (-(1 + (-y))) ((-1) + y) ?_) ?_
  · refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv 1 (-y)) ?_
    exact Q'.add_eqv_congr_left (-1) (-(-y)) y (Q'.neg_neg_eqv y)
  · refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv 1 (-1) y)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (1 + (-1)) 0 y (Q'.add_neg_self_eqv 1)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' y)

/-! ## 3. The decimation trajectory and the EXACT decimation relation

`bpow b k = bᵏ` (as a positive rational), `yk = c·τ/bᵏ`, `sepCReal = e^{−yk}`.
The exact decimation relation `yk = b · y_{k+1}` (`decimation_exponent`) holds at
`Q'.eqv` because `bᵏ = b · bᵏ⁺¹⁻¹`; hence the separator decimation
`sepCReal_k ≃ e^{−(b · y_{k+1})}` (`decimation_step`).  This is what makes the
orbit a genuine RG decimation orbit. -/

/-- `bᵏ` as a `Q'` (cast of the `Nat` power `b^k`). -/
def bpow (b k : Nat) : Q' := Q'.ofNat (b ^ k)

/-- `bᵏ > 0` for `b ≥ 1`. -/
theorem bpow_pos (b k : Nat) (hb : 1 ≤ b) : (0 : Q') < bpow b k := by
  show (0 : Int) * ((bpow b k).den : Int) < (bpow b k).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  show (0 : Int) < (Int.ofNat (b ^ k))
  have : 0 < b ^ k := Nat.pow_pos hb
  exact Int.ofNat_lt.mpr this

/-- The decimation exponent `y_k = c·τ / bᵏ`, a positive rational. -/
def yk (c τ : Q') (b k : Nat) (hb : 1 ≤ b) : Q' :=
  (c * τ) * Q'.recipPos (bpow b k) (bpow_pos b k hb)

/-- `y_k > 0` when `c, τ > 0`. -/
theorem yk_pos (c τ : Q') (b k : Nat) (hb : 1 ≤ b)
    (hc : (0 : Q') < c) (hτ : (0 : Q') < τ) : (0 : Q') < yk c τ b k hb :=
  Q'.mul_pos (Q'.mul_pos hc hτ) (Q'.recipPos_pos (bpow b k) (bpow_pos b k hb))

/-- `y_k ≥ 0`. -/
theorem yk_nonneg (c τ : Q') (b k : Nat) (hb : 1 ≤ b)
    (hc : (0 : Q') < c) (hτ : (0 : Q') < τ) : (0 : Q') ≤ yk c τ b k hb :=
  Q'.le_of_lt (yk_pos c τ b k hb hc hτ)

/-- The separator `sep_k = e^{−y_k}` (a `CReal`). -/
def sepCReal (c τ : Q') (b k : Nat) (hb : 1 ≤ b)
    (hc : (0 : Q') < c) (hτ : (0 : Q') < τ) : CReal :=
  ExpNeg.expNeg (yk c τ b k hb) (yk_nonneg c τ b k hb hc hτ)

/-- **The recip decimation step** `recip(bᵏ) ≃ b · recip(bᵏ⁺¹)` (at `Q'.eqv`).
Both equal `1/bᵏ`; cross-multiplying reduces to the `Nat` identity
`b · bᵏ = bᵏ⁺¹`. -/
theorem bpow_recip_step (b k : Nat) (hb : 1 ≤ b) :
    (Q'.recipPos (bpow b k) (bpow_pos b k hb)).eqv
      (Q'.ofNat b * Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb)) := by
  -- `.eqv` is `LHS.num · RHS.den = RHS.num · LHS.den` (cross-product over Int).
  show (Q'.recipPos (bpow b k) (bpow_pos b k hb)).num
        * ((Q'.ofNat b * Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb)).den : Int)
      = (Q'.ofNat b * Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb)).num
        * ((Q'.recipPos (bpow b k) (bpow_pos b k hb)).den : Int)
  -- Numerators / denominators of the two recips and the product, as Int.
  have hLnum : (Q'.recipPos (bpow b k) (bpow_pos b k hb)).num = (1 : Int) := by
    rw [Q'.recipPos_num]; rfl
  have hLden : ((Q'.recipPos (bpow b k) (bpow_pos b k hb)).den : Int)
      = Int.ofNat (b ^ k) := by rw [Q'.recipPos_den]; rfl
  have hRnum : (Q'.ofNat b * Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb)).num
      = Int.ofNat b := by
    show (Q'.ofNat b).num * (Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb)).num
        = Int.ofNat b
    rw [Q'.recipPos_num]
    show Int.ofNat b * (1 : Int) = Int.ofNat b
    rw [Int.mul_one]
  -- (recipPos (b^{k+1})).den = b^{k+1} as a Nat.
  have hRecDenNat : (Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb)).den = b ^ (k + 1) := by
    have hmk : (Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb)).den
        = (bpow b (k + 1)).num.toNat := Q'.mkPos_den _ _ _
    rw [hmk]
    show (Int.ofNat (b ^ (k + 1))).toNat = b ^ (k + 1)
    rfl
  -- The product's denominator (as a Nat) is 1 · b^{k+1} = b^{k+1}.
  have hRdenNat : (Q'.ofNat b * Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb)).den
      = b ^ (k + 1) := by
    show (Q'.ofNat b).den * (Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb)).den
        = b ^ (k + 1)
    have h1 : (Q'.ofNat b).den = 1 := rfl
    rw [h1, hRecDenNat, Nat.one_mul]
  have hRden : ((Q'.ofNat b * Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb)).den : Int)
      = Int.ofNat (b ^ (k + 1)) := by
    rw [hRdenNat]; rfl
  rw [hLnum, hLden, hRnum, hRden, Int.one_mul]
  -- Goal: ofNat (b^{k+1}) = ofNat b * ofNat (b^k)
  have hpow : b ^ (k + 1) = b * b ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hpow]
  show Int.ofNat (b * b ^ k) = Int.ofNat b * Int.ofNat (b ^ k)
  rfl

/-- **The EXACT decimation exponent relation** `y_k = b · y_{k+1}` (at `Q'.eqv`).
Because `bᵏ = b · bᵏ⁺¹⁻¹`, the exponent of one decimated block is `b` times the
next: `c·τ/bᵏ = b · (c·τ/bᵏ⁺¹)`.  This is the exact heat-semigroup decimation,
not an arbitrary choice. -/
theorem decimation_exponent (c τ : Q') (b k : Nat) (hb : 1 ≤ b) :
    (yk c τ b k hb).eqv (Q'.ofNat b * yk c τ b (k + 1) hb) := by
  -- yk k = (cτ)·recip(bᵏ) ≃ (cτ)·(b·recip(bᵏ⁺¹)) ≃ b·((cτ)·recip(bᵏ⁺¹)) = b·yk(k+1)
  show ((c * τ) * Q'.recipPos (bpow b k) (bpow_pos b k hb)).eqv
    (Q'.ofNat b * ((c * τ) * Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb)))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (c * τ) _ _ (bpow_recip_step b k hb)) ?_
  -- (cτ)·(b·r₁) ≃ (b·r₁)·(cτ) ≃ b·(r₁·(cτ)) ≃ b·((cτ)·r₁)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv (c * τ)
      (Q'.ofNat b * Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (Q'.ofNat b)
      (Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb)) (c * τ)) ?_
  exact Q'.mul_eqv_congr_left (Q'.ofNat b) _ _
    (Q'.mul_comm_eqv (Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb)) (c * τ))

/-- **The decimation separator relation (EXACT, separator form):**
`sep_k ≃ e^{−(b · y_{k+1})}`.  Transports `decimation_exponent` across `expNeg`'s
`eqv`-congruence (`expNeg_eqv_congr`).  Together with the exponential
multiplicativity `e^{−(b·z)} = (e^{−z})^b` this is the gap-separator decimation
law `sep_k = (sep_{k+1})^b`; the exponent relation is the exact content. -/
theorem decimation_step (c τ : Q') (b k : Nat) (hb : 1 ≤ b)
    (hc : (0 : Q') < c) (hτ : (0 : Q') < τ) :
    CReal.Equiv (sepCReal c τ b k hb hc hτ)
      (ExpNeg.expNeg (Q'.ofNat b * yk c τ b (k + 1) hb)
        (Q'.le_of_lt (Q'.mul_pos (by
            show (0 : Q') < Q'.ofNat b
            show (0 : Int) * ((Q'.ofNat b).den : Int) < (Q'.ofNat b).num * (1 : Int)
            rw [Int.zero_mul, Int.mul_one]
            show (0 : Int) < Int.ofNat b
            exact Int.ofNat_lt.mpr hb)
          (yk_pos c τ b (k + 1) hb hc hτ)))) :=
  expNeg_eqv_congr _ _ (decimation_exponent c τ b k hb)

/-! ## 4. The physical gap trajectory and its two-sided bound

`physGap_k = (bᵏ/a₀) · margin_k`.  The factor `physFactor k = bᵏ/a₀` is a
positive rational; scaling the margin bounds (§2) by it gives the physical gap
bounds.  The constants collapse: `physFactor·y_k ≃ cτ/a₀` and
`physFactor·(y_k/2) ≃ cτ/(2a₀)`, by `bᵏ·(1/bᵏ) ≃ 1`. -/

/-- The physical-gap rational prefactor `physFactor k = bᵏ / a₀`. -/
def physFactor (a₀ : Q') (ha₀ : (0 : Q') < a₀) (b k : Nat) (hb : 1 ≤ b) : Q' :=
  bpow b k * Q'.recipPos a₀ ha₀

/-- `physFactor k ≥ 0`. -/
theorem physFactor_nonneg (a₀ : Q') (ha₀ : (0 : Q') < a₀) (b k : Nat) (hb : 1 ≤ b) :
    (0 : Q') ≤ physFactor a₀ ha₀ b k hb :=
  Q'.le_of_lt (Q'.mul_pos (bpow_pos b k hb) (Q'.recipPos_pos a₀ ha₀))

/-- The physical gap `physGap_k = (bᵏ/a₀) · margin_k` (a `CReal`). -/
def physGap (c τ a₀ : Q') (ha₀ : (0 : Q') < a₀) (b k : Nat) (hb : 1 ≤ b)
    (hc : (0 : Q') < c) (hτ : (0 : Q') < τ) : CReal :=
  CReal.mul (CReal.ofQ' (physFactor a₀ ha₀ b k hb))
    (marginCReal (yk c τ b k hb) (yk_nonneg c τ b k hb hc hτ))

/-- **The finiteness ceiling** `physGapMax = c·τ / a₀`. -/
def physGapMax (c τ a₀ : Q') (ha₀ : (0 : Q') < a₀) : Q' :=
  Q'.divPos (c * τ) a₀ ha₀

/-- **The positive floor** `physGapMin = c·τ / (2 a₀) = half · (cτ/a₀)`. -/
def physGapMin (c τ a₀ : Q') (ha₀ : (0 : Q') < a₀) : Q' :=
  half * Q'.divPos (c * τ) a₀ ha₀

/-- `physGapMin > 0` for `c, τ > 0` (a product of positives). -/
theorem physGapMin_pos (c τ a₀ : Q') (ha₀ : (0 : Q') < a₀)
    (hc : (0 : Q') < c) (hτ : (0 : Q') < τ) :
    (0 : Q') < physGapMin c τ a₀ ha₀ := by
  refine Q'.mul_pos (by decide) ?_
  exact Q'.divPos_pos (c * τ) a₀ ha₀ (Q'.mul_pos hc hτ)

/-- **`geRat` scaling**: scale a sound lower bound by a nonnegative rational.
`0 ≤ d → geRat y b → geRat (d·y) (d·b)`.  Dual of `CReal.leRat_smul_nonneg`. -/
theorem geRat_smul_nonneg {d : Q'} (hd : (0 : Q') ≤ d) {y : CReal} {b : Q'}
    (h : ExpPos.geRat y b) :
    ExpPos.geRat (CReal.mul (CReal.ofQ' d) y) (d * b) := by
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le hd hε
  obtain ⟨N, hN⟩ := h δ hδpos
  refine ⟨N, fun n hn => ?_⟩
  have hyb : b ≤ y.approx n + δ := hN n hn
  -- d·b ≤ d·(y_n + δ) = d·y_n + d·δ ≤ d·y_n + ε ; and (mul (ofQ' d) y).approx n = d · y_n
  have s1 : d * b ≤ d * (y.approx n + δ) :=
    Q'.mul_le_mul_of_nonneg_left b (y.approx n + δ) d hyb hd
  have e1 : (d * (y.approx n + δ)).eqv (d * y.approx n + d * δ) := Q'.mul_add_eqv d (y.approx n) δ
  have s2 : d * y.approx n + d * δ ≤ d * y.approx n + ε :=
    Q'.add_le_add_left (d * y.approx n) (d * δ) ε hδ
  -- (mul (ofQ' d) y).approx n = (ofQ' d).approx n * y.approx n = d * y.approx n
  show d * b ≤ d * y.approx n + ε
  exact Q'.le_trans' _ _ _ s1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) s2)

/-- The constant collapse `physFactor k · y_k ≃ c·τ/a₀`.
`(bᵏ·(1/a₀)) · ((cτ)·(1/bᵏ)) ≃ (cτ)·(1/a₀) · (bᵏ·(1/bᵏ)) ≃ (cτ)·(1/a₀) = divPos`. -/
theorem physFactor_mul_yk_eqv (c τ a₀ : Q') (ha₀ : (0 : Q') < a₀) (b k : Nat)
    (hb : 1 ≤ b) :
    (physFactor a₀ ha₀ b k hb * yk c τ b k hb).eqv (Q'.divPos (c * τ) a₀ ha₀) := by
  -- physFactor = bᵏ · ra₀ ; yk = cτ · rbk  (rbk = recipPos bᵏ, ra₀ = recipPos a₀).
  -- divPos (cτ) a₀ = (cτ) · ra₀ (definitionally).
  show ((bpow b k * Q'.recipPos a₀ ha₀)
        * ((c * τ) * Q'.recipPos (bpow b k) (bpow_pos b k hb))).eqv
      ((c * τ) * Q'.recipPos a₀ ha₀)
  -- (bᵏ·ra₀)·((cτ)·rbk) ≃ ((cτ)·rbk)·(bᵏ·ra₀) ≃ (cτ)·(rbk·(bᵏ·ra₀))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv (bpow b k * Q'.recipPos a₀ ha₀)
      ((c * τ) * Q'.recipPos (bpow b k) (bpow_pos b k hb))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (c * τ) (Q'.recipPos (bpow b k) (bpow_pos b k hb))
      (bpow b k * Q'.recipPos a₀ ha₀)) ?_
  refine Q'.mul_eqv_congr_left (c * τ) _ _ ?_
  -- rbk·(bᵏ·ra₀) ≃ (rbk·bᵏ)·ra₀ ≃ (bᵏ·rbk)·ra₀ ≃ 1·ra₀ ≃ ra₀
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.recipPos (bpow b k) (bpow_pos b k hb)) (bpow b k)
      (Q'.recipPos a₀ ha₀))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ (bpow b k * Q'.recipPos (bpow b k) (bpow_pos b k hb))
      (Q'.recipPos a₀ ha₀)
      (Q'.mul_comm_eqv (Q'.recipPos (bpow b k) (bpow_pos b k hb)) (bpow b k))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (bpow b k * Q'.recipPos (bpow b k) (bpow_pos b k hb)) 1
      (Q'.recipPos a₀ ha₀)
      (Q'.mul_recipPos_eqv (bpow b k) (bpow_pos b k hb))) ?_
  exact Q'.one_mul_eqv (Q'.recipPos a₀ ha₀)

/-- The half-scaled collapse `physFactor k · (half·y_k) ≃ physGapMin`. -/
theorem physFactor_mul_half_yk_eqv (c τ a₀ : Q') (ha₀ : (0 : Q') < a₀) (b k : Nat)
    (hb : 1 ≤ b) :
    (physFactor a₀ ha₀ b k hb * (half * yk c τ b k hb)).eqv
      (physGapMin c τ a₀ ha₀) := by
  -- physFactor·(half·yk) ≃ half·(physFactor·yk) ≃ half·divPos = physGapMin
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (physFactor a₀ ha₀ b k hb) (half * yk c τ b k hb)
      (yk c τ b k hb * half) (Q'.mul_comm_eqv half (yk c τ b k hb))) ?_
  -- physFactor·(yk·half) ≃ (physFactor·yk)·half ≃ (divPos)·half ≃ half·divPos
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (physFactor a₀ ha₀ b k hb) (yk c τ b k hb) half)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ half (physFactor_mul_yk_eqv c τ a₀ ha₀ b k hb)) ?_
  exact Q'.mul_comm_eqv (Q'.divPos (c * τ) a₀ ha₀) half

/-- **`physGap_upper`** — the finiteness ceiling, for ALL `k` with `y_k ≤ 1`:
`leRat (physGap_k) (physGapMax) = leRat (physGap_k) (cτ/a₀)`.  From the margin
upper bound `margin ≤ y_k`, scaled by `physFactor ≥ 0`, and the collapse
`physFactor·y_k ≃ cτ/a₀`. -/
theorem physGap_upper (c τ a₀ : Q') (ha₀ : (0 : Q') < a₀) (b k : Nat) (hb : 1 ≤ b)
    (hc : (0 : Q') < c) (hτ : (0 : Q') < τ)
    (hyk1 : yk c τ b k hb ≤ 1) :
    CReal.leRat (physGap c τ a₀ ha₀ b k hb hc hτ) (physGapMax c τ a₀ ha₀) := by
  -- margin ≤ y_k
  have hmargin : CReal.leRat (marginCReal (yk c τ b k hb) (yk_nonneg c τ b k hb hc hτ))
      (yk c τ b k hb) :=
    marginCReal_leRat (yk c τ b k hb) (yk_nonneg c τ b k hb hc hτ) hyk1
  -- scale by physFactor
  have hscaled : CReal.leRat (physGap c τ a₀ ha₀ b k hb hc hτ)
      (physFactor a₀ ha₀ b k hb * yk c τ b k hb) :=
    CReal.leRat_smul_nonneg (physFactor_nonneg a₀ ha₀ b k hb) hmargin
  refine CReal.leRat_mono hscaled ?_
  exact Q'.le_of_eqv (physFactor_mul_yk_eqv c τ a₀ ha₀ b k hb)

/-- **`physGap_lower`** — the positive floor, for all `k` with `y_k ≤ 1`:
`geRat (physGap_k) (physGapMin) = geRat (physGap_k) (cτ/(2a₀))`.  From the margin
lower bound `margin ≥ y_k/2`, scaled by `physFactor ≥ 0`, and the collapse
`physFactor·(y_k/2) ≃ cτ/(2a₀)`. -/
theorem physGap_lower (c τ a₀ : Q') (ha₀ : (0 : Q') < a₀) (b k : Nat) (hb : 1 ≤ b)
    (hc : (0 : Q') < c) (hτ : (0 : Q') < τ)
    (hyk1 : yk c τ b k hb ≤ 1) :
    ExpPos.geRat (physGap c τ a₀ ha₀ b k hb hc hτ) (physGapMin c τ a₀ ha₀) := by
  -- margin ≥ half·y_k
  have hmargin : ExpPos.geRat (marginCReal (yk c τ b k hb) (yk_nonneg c τ b k hb hc hτ))
      (half * yk c τ b k hb) :=
    marginCReal_geRat_half (yk c τ b k hb) (yk_nonneg c τ b k hb hc hτ) hyk1
  -- scale by physFactor
  have hscaled : ExpPos.geRat (physGap c τ a₀ ha₀ b k hb hc hτ)
      (physFactor a₀ ha₀ b k hb * (half * yk c τ b k hb)) :=
    geRat_smul_nonneg (physFactor_nonneg a₀ ha₀ b k hb) hmargin
  refine ExpPos.geRat_mono hscaled ?_
  exact Q'.le_of_eqv (Q'.eqv_symm (physFactor_mul_half_yk_eqv c τ a₀ ha₀ b k hb))

/-! ## 5. The headline — the unconditional positive-and-finite continuum gap

The small-spacing entry index `k₀`: the first `k` with `y_k ≤ 1`.  Since
`y_k = cτ/bᵏ → 0` and `b ≥ 2`, such a `k₀` exists; we take it as a parameter
witnessed by `hk₀` (the model's "enter the small-coupling window" datum).  For
`k ≥ k₀` the lower floor holds; the upper ceiling holds for every `k` with
`y_k ≤ 1` (in particular all `k ≥ k₀`). -/

/-- The monotone decrease `y_{k+1} ≤ y_k` (the exponent shrinks each step), so
once `y_{k₀} ≤ 1` it stays `≤ 1`.  `y_{k+1} = y_k / b ≤ y_k` since `b ≥ 1`. -/
theorem yk_antitone (c τ : Q') (b k : Nat) (hb : 1 ≤ b)
    (hc : (0 : Q') < c) (hτ : (0 : Q') < τ) :
    yk c τ b (k + 1) hb ≤ yk c τ b k hb := by
  -- yk (k+1) = (1/b)·yk k  (from decimation_exponent: yk k ≃ b·yk(k+1)), and 1/b ≤ 1.
  -- Direct: yk = cτ·recip(b^k); recip(b^{k+1}) ≤ recip(b^k) since b^k ≤ b^{k+1}.
  have hcτ : (0 : Q') ≤ c * τ := Q'.le_of_lt (Q'.mul_pos hc hτ)
  have hrec_le : Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb)
      ≤ Q'.recipPos (bpow b k) (bpow_pos b k hb) := by
    -- recip is antitone: b^k ≤ b^{k+1} ⟹ 1/b^{k+1} ≤ 1/b^k.
    -- Cross-multiplied: recip(b^{k+1}).num·recip(b^k).den ≤ recip(b^k).num·recip(b^{k+1}).den
    show (Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb)).num
          * ((Q'.recipPos (bpow b k) (bpow_pos b k hb)).den : Int)
        ≤ (Q'.recipPos (bpow b k) (bpow_pos b k hb)).num
          * ((Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb)).den : Int)
    rw [Q'.recipPos_num, Q'.recipPos_num, Q'.recipPos_den, Q'.recipPos_den]
    -- (b^{k+1}).den · (b^k).num ≤ (b^k).den · (b^{k+1}).num
    show ((bpow b (k + 1)).den : Int) * (bpow b k).num
        ≤ ((bpow b k).den : Int) * (bpow b (k + 1)).num
    show (1 : Int) * (Int.ofNat (b ^ k)) ≤ (1 : Int) * (Int.ofNat (b ^ (k + 1)))
    rw [Int.one_mul, Int.one_mul]
    have : b ^ k ≤ b ^ (k + 1) := by
      rw [Nat.pow_succ]; exact Nat.le_mul_of_pos_right (b ^ k) hb
    exact Int.ofNat_le.mpr this
  show (c * τ) * Q'.recipPos (bpow b (k + 1)) (bpow_pos b (k + 1) hb)
      ≤ (c * τ) * Q'.recipPos (bpow b k) (bpow_pos b k hb)
  exact Q'.mul_le_mul_of_nonneg_left _ _ (c * τ) hrec_le hcτ

/-- Once `y_{k₀} ≤ 1`, `y_k ≤ 1` for all `k ≥ k₀` (by antitonicity). -/
theorem yk_le_one_of_ge (c τ : Q') (b k₀ : Nat) (hb : 1 ≤ b)
    (hc : (0 : Q') < c) (hτ : (0 : Q') < τ) (hk₀ : yk c τ b k₀ hb ≤ 1) :
    ∀ k, k₀ ≤ k → yk c τ b k hb ≤ 1 := by
  intro k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  -- yk (k₀ + d) ≤ yk k₀ ≤ 1
  induction d with
  | zero => exact hk₀
  | succ d ih =>
      have hstep : yk c τ b (k₀ + d + 1) hb ≤ yk c τ b (k₀ + d) hb :=
        yk_antitone c τ b (k₀ + d) hb hc hτ
      exact Q'.le_trans' _ _ _ hstep (ih (Nat.le_add_right k₀ d))

/-- **THE UNCONDITIONAL GAP.**  Given the model parameters `c, τ, a₀ > 0`,
`b ≥ 2`, and the small-spacing entry datum `k₀` (the first scale with
`y_{k₀} ≤ 1` — a property of the explicit model, witnessed by `hk₀`), there is a
positive floor `physGapMin = cτ/(2a₀)` and a finiteness ceiling
`physGapMax = cτ/a₀` such that for ALL `k ≥ k₀`:

    physGapMin  ≤  physGap_k  ≤  physGapMax              (as `CReal` limits),

uniformly as the spacing `a_k = a₀/bᵏ → 0`.  NO hypotheses beyond the explicit
positive parameters — the bound is DERIVED from the exp inequalities and the
exact decimation orbit.  This is the FIRST unconditional positive-and-finite
continuum gap in the development, on the δ = 0 decimation line (NOT the 4D YM
gap; see the module header and §6). -/
def hierarchical_physGapMin_pos (c τ a₀ : Q') (ha₀ : (0 : Q') < a₀)
    (b k₀ : Nat) (hb : 2 ≤ b) (hc : (0 : Q') < c) (hτ : (0 : Q') < τ)
    (hk₀ : yk c τ b k₀ (Nat.le_trans (by decide) hb) ≤ 1) :
    Σ' physGapMin' : Q', Σ' physGapMax' : Q',
      (0 : Q') < physGapMin' ∧
        ∀ k, k₀ ≤ k →
          ExpPos.geRat
            (physGap c τ a₀ ha₀ b k (Nat.le_trans (by decide) hb) hc hτ) physGapMin' ∧
          CReal.leRat
            (physGap c τ a₀ ha₀ b k (Nat.le_trans (by decide) hb) hc hτ) physGapMax' := by
  have hb1 : 1 ≤ b := Nat.le_trans (by decide) hb
  refine ⟨physGapMin c τ a₀ ha₀, physGapMax c τ a₀ ha₀,
    physGapMin_pos c τ a₀ ha₀ hc hτ, ?_⟩
  intro k hk
  have hyk1 : yk c τ b k hb1 ≤ 1 := yk_le_one_of_ge c τ b k₀ hb1 hc hτ hk₀ k hk
  exact ⟨physGap_lower c τ a₀ ha₀ b k hb1 hc hτ hyk1,
         physGap_upper c τ a₀ ha₀ b k hb1 hc hτ hyk1⟩

/-! ## 6. Doc-section (the honesty contract, restated)

**What is proved (genuine, unconditional).**  On the EXACT heat-kernel
DECIMATION LINE — heat-kernel time `t_k = τ/bᵏ`, separator `sep_k = e^{−cτ/bᵏ}`,
spacing `a_k = a₀/bᵏ` — the physical gap

    physGap_k = (1 − sep_k)/a_k = margin_k · bᵏ/a₀

is UNIFORMLY two-sided bounded as `a_k → 0`:

    cτ/(2a₀)  ≤  physGap_k  ≤  cτ/a₀         for all  k ≥ k₀,

with NO hypotheses beyond the explicit positive model parameters `c, τ, a₀, b`.
The derivation is real: the LOWER bound is the scalar `1 − e^{−y} ≥ y/2`
(reused), the UPPER bound is `1 − e^{−y} ≤ y` (proved here from the alternating
series), and the orbit is the EXACT decimation orbit `y_k = b·y_{k+1}`
(`decimation_exponent` / `decimation_step`), not a convenient choice.  This is
the FIRST unconditional positive-AND-finite continuum gap (dimensional
transmutation) in the development.

**What is NOT proved (the open 4D content).**  This is NOT the 4D Yang–Mills mass
gap.  The decimation line is the heat-semigroup half of a Migdal–Kadanoff block
step, where the separator commutes with the heat semigroup EXACTLY (so the orbit
is exactly soluble) and is dimension-agnostic (decimation does not see the
spacetime dimension `d`).  The genuine 4D content is the bond-moving residual `δ`
— the deviation between this exact decimation orbit and the physical
gauge-invariant separator — which is NOT controlled here and remains open.  The
number above is therefore a dimensional-transmutation result for the
exactly-soluble RG-fixed-point model, not a solution of the Clay problem.

**On connecting to the existing floor framework.**  The margins here are `CReal`,
so the floor/ceiling are the SOUND limit-order predicates `ExpPos.geRat` /
`CReal.leRat` (the CReal-correct form of `c ≤ margin/a ≤ C`).  The standalone
unconditional theorem `hierarchical_physGapMin_pos` is the deliverable.  A bridge
into a `divPos`-based rational floor would need a CReal-variant of that floor
whose `floor`/`finiteness` fields are `geRat`/`leRat` on a `CReal` separator
margin; that variant is noted here, not forced, to avoid a lossy
rational-projection of the genuine `CReal` margins.
-/

end YMGap.Continuum.HierarchicalGap

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HierarchicalGap.y_invSucc_le_one
#print axioms YMGap.Continuum.HierarchicalGap.termAbs_antitone_step
#print axioms YMGap.Continuum.HierarchicalGap.term_parity
#print axioms YMGap.Continuum.HierarchicalGap.term_even_nonneg
#print axioms YMGap.Continuum.HierarchicalGap.term_pair_nonneg
#print axioms YMGap.Continuum.HierarchicalGap.partialSum_ge_oneSub_aux
#print axioms YMGap.Continuum.HierarchicalGap.partialSum_ge_oneSub
#print axioms YMGap.Continuum.HierarchicalGap.expNeg_geRat_oneSubArg
#print axioms YMGap.Continuum.HierarchicalGap.geRat_neg_of_leRat
#print axioms YMGap.Continuum.HierarchicalGap.leRat_neg_of_geRat
#print axioms YMGap.Continuum.HierarchicalGap.geRat_add
#print axioms YMGap.Continuum.HierarchicalGap.marginCReal_geRat_half
#print axioms YMGap.Continuum.HierarchicalGap.marginCReal_leRat
#print axioms YMGap.Continuum.HierarchicalGap.bpow_recip_step
#print axioms YMGap.Continuum.HierarchicalGap.decimation_exponent
#print axioms YMGap.Continuum.HierarchicalGap.decimation_step
#print axioms YMGap.Continuum.HierarchicalGap.geRat_smul_nonneg
#print axioms YMGap.Continuum.HierarchicalGap.physFactor_mul_yk_eqv
#print axioms YMGap.Continuum.HierarchicalGap.physFactor_mul_half_yk_eqv
#print axioms YMGap.Continuum.HierarchicalGap.physGap_upper
#print axioms YMGap.Continuum.HierarchicalGap.physGap_lower
#print axioms YMGap.Continuum.HierarchicalGap.yk_antitone
#print axioms YMGap.Continuum.HierarchicalGap.yk_le_one_of_ge
#print axioms YMGap.Continuum.HierarchicalGap.hierarchical_physGapMin_pos
