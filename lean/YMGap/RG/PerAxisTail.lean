/-
**Full (B1) closure: the polynomial-geometric per-axis character tail.**

Assembles all the exp machinery into the COMPLETE per-axis character-tail bound
(`docs/sun-uniform-cap-factorization.md`, atom (B1) with the polynomial factor):

    Σ_{m<N} (poly-weight w m)·e^{−g(m)}  ≤  B₀·H^{d+1}

for a per-term exponent `g(m) ≥ a·m` (linear lower bound) with `e^{−a} ≤ ρ < 1`,
a polynomial weight `w` termwise dominated by `B₀·C(m+d,d)`, and `1 + ρ·H ≤ H`.

This is the per-axis factor `S_i = Σ_m (m+1)^{2q_i} e^{−t h_i(m)}`: the weight is
`(m+1)^{2q_i}` (`d = 2q_i`), the exponent `g(m) = t·h_i(m) ≥ (t q_i/2)·m =: a·m`
(the linear lower bound from `h_i(m) = (q_i/2)·m·(1+m/N) ≥ (q_i/2)·m`).  The
chain:

  * `e^{−a·m} ≤ ρ^m`                         (`ExpGeomBound.expNeg_mul_le_pow`)
  * `e^{−g(m)} ≤ ρ^m`                        (`expNeg_antitone_leRat`, `g(m) ≥ a·m`)
  * `w m · e^{−g(m)} ≤ w m · ρ^m`            (`CReal.leRat_smul_nonneg`)
  * `Σ … ≤ Σ w m · ρ^m`                      (`CReal.leRat_csum`)
  * `Σ w m · ρ^m ≤ B₀·H^{d+1}`               (`PolylogTail.weightedGeomSum_le`)

So the per-axis tail closes at a single explicit rational `B₀·H^{d+1}` — the
genuine polynomial-geometric majorant, no window, beating the polynomial factor
the rational Padé surrogate cannot (notes §6).  This is the full discharge of
the per-axis `AxisFactorBound` from the constructive exp stack.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Constructive.ExpGeomBound
import YMGap.Constructive.CRealSum
import YMGap.Constructive.CRealMulMono
import YMGap.Constructive.CharacterTail
import YMGap.RG.CharacterTailAntitone
import YMGap.RG.PolylogTail

namespace YMGap.RG

open YMGap.Constructive
open YMGap.Constructive.CharacterTail

/-- **The complete polynomial-geometric per-axis character tail bound.**
`Σ_{m<N} w(m)·e^{−g(m)} ≤ B₀·H^{d+1}`, for a per-term exponent `g(m) ≥ a·m`
with `e^{−a} ≤ ρ`, a nonnegative polynomial weight `w` dominated by
`B₀·C(m+d,d)`, and the geometric recurrence `1 + ρ·H ≤ H`.

This is the per-axis character-tail factor `S_i`, closed at a single explicit
rational majorant from the constructive exp stack. -/
theorem expNeg_poly_csum_le
    (a ρ H B0 : Q') (d : Nat) (w g : Nat → Q')
    (ha : (0 : Q') ≤ a) (hρ0 : (0 : Q') ≤ ρ) (hH : (0 : Q') ≤ H) (hB0 : (0 : Q') ≤ B0)
    (hg0 : ∀ m, (0 : Q') ≤ g m)
    (hρ : CReal.leRat (ExpNeg.expNeg a ha) ρ)
    (hge : ∀ m, a * Q'.ofNat m ≤ g m)
    (hw0 : ∀ m, (0 : Q') ≤ w m)
    (hdom : ∀ n, w n ≤ B0 * (Q'.ofNat (binom (n + d) d)))
    (hrec : (1 : Q') + ρ * H ≤ H) :
    ∀ N, CReal.leRat
      (CReal.csum (fun m => CReal.mul (CReal.ofQ' (w m)) (ExpNeg.expNeg (g m) (hg0 m))) N)
      (B0 * H ^ (d + 1)) := by
  intro N
  -- term: e^{−g(m)} ≤ ρ^m  (geometric domination + antitonicity through g(m) ≥ a·m)
  have hterm_exp : ∀ m, CReal.leRat (ExpNeg.expNeg (g m) (hg0 m)) (ρ ^ m) := by
    intro m
    exact expNeg_antitone_leRat
      (Q'.mul_nonneg a (Q'.ofNat m) ha (ofNat_nonneg m)) (hge m)
      (ρ ^ m) (Q'.pow_nonneg ρ hρ0 m)
      (expNeg_mul_le_pow a ρ ha hρ0 hρ m)
  -- weighted term: w(m)·e^{−g(m)} ≤ w(m)·ρ^m
  refine CReal.leRat_mono
    (CReal.leRat_csum _ (fun m => w m * ρ ^ m)
      (fun m => CReal.leRat_smul_nonneg (hw0 m) (hterm_exp m)) N) ?_
  -- Σ w(m)·ρ^m ≤ B₀·H^{d+1}
  exact weightedGeomSum_le hρ0 hH hB0 hrec d w hdom N

/-! ## The TIGHT per-axis tail (term-ratio route)

`expNeg_poly_csum_le` above (via `weightedGeomSum`) is FINITE but loose (its
`B₀ = (2q)!`-style constant is astronomically larger than the true tail), so it
does NOT satisfy the cap.  The TIGHT bound uses the term-RATIO closure
`CharacterTail.geom_series_le`: with a polynomial weight `w` of bounded ratio
`w(m+1) ≤ P·w(m)` and geometric base `ρ` (`e^{−a} ≤ ρ`, `g(m) ≥ a·m`), the
character tail majorant `f(m) = w(m)·ρ^m` has uniform ratio `f(m+1) ≤ (P·ρ)·f(m)`,
so it sums to `≤ H` under the one-step recurrence `w(0) + (P·ρ)·H ≤ H`.

For SU(N): `w(m) = (m+1)^{2q_i}` has ratio `P = 4^{q_i}` (since
`(m+2)/(m+1) ≤ 2`), `ρ = e^{−t h_i(1)}`, so `P·ρ = (4 e^{−t(N+1)/(2N)})^{q_i} =
b^{q_i} < 1` — the tail closes at `1/(1−b^{q_i})`, giving `s_i ≤ b^{q_i}/(1−b^{q_i})`
(tiny), summable to the cap.  This is the correct per-axis tool. -/

/-- Middle-swap of a 4-fold product: `(A·B)·(C·D) ≃ (A·C)·(B·D)`. -/
theorem mul_mul_swap_eqv (A B C D : Q') :
    ((A * B) * (C * D)).eqv ((A * C) * (B * D)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A B (C * D)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left A _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv B C D))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left A _ _ (Q'.mul_eqv_congr_right _ _ D (Q'.mul_comm_eqv B C))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left A _ _ (Q'.mul_assoc_eqv C B D)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv A C (B * D))

/-- **The TIGHT per-axis character-tail bound.**
`Σ_{m<N} w(m)·e^{−g(m)} ≤ H`, given `e^{−a} ≤ ρ`, the linear lower bound
`g(m) ≥ a·m`, a nonnegative polynomial weight `w` of bounded ratio
`w(m+1) ≤ P·w(m)`, and the geometric recurrence `w(0) + (P·ρ)·H ≤ H`.

The majorant `f(m) = w(m)·ρ^m` has uniform term-ratio `f(m+1) ≤ (P·ρ)·f(m)`, so
`CharacterTail.geom_series_le` sums it to `≤ H`; the character term is `≤ f(m)`
(geometric domination of `e^{−g(m)}` + `leRat_smul_nonneg`); `leRat_csum`
finishes.  With `P·ρ < 1` this closes the per-axis tail at `H = 1/(1−P·ρ)` —
the tight rational, NOT the loose `weightedGeomSum` constant. -/
theorem charTail_geom_le
    (a ρ P H : Q') (w g : Nat → Q')
    (ha : (0 : Q') ≤ a) (hρ0 : (0 : Q') ≤ ρ) (hP0 : (0 : Q') ≤ P) (hH : (0 : Q') ≤ H)
    (hg0 : ∀ m, (0 : Q') ≤ g m) (hw0 : ∀ m, (0 : Q') ≤ w m)
    (hρ : CReal.leRat (ExpNeg.expNeg a ha) ρ)
    (hge : ∀ m, a * Q'.ofNat m ≤ g m)
    (hwratio : ∀ m, w (m + 1) ≤ P * w m)
    (hrec : w 0 + (P * ρ) * H ≤ H) :
    ∀ N, CReal.leRat
      (CReal.csum (fun m => CReal.mul (CReal.ofQ' (w m)) (ExpNeg.expNeg (g m) (hg0 m))) N)
      H := by
  intro N
  -- the Q' majorant f(m) = w(m)·ρ^m
  -- (1) per-term geometric domination of the character term: char(m) ≤ f(m)
  have hterm : ∀ m,
      CReal.leRat (CReal.mul (CReal.ofQ' (w m)) (ExpNeg.expNeg (g m) (hg0 m))) (w m * ρ ^ m) := by
    intro m
    have hexp : CReal.leRat (ExpNeg.expNeg (g m) (hg0 m)) (ρ ^ m) :=
      expNeg_antitone_leRat
        (Q'.mul_nonneg a (Q'.ofNat m) ha (ofNat_nonneg m)) (hge m)
        (ρ ^ m) (Q'.pow_nonneg ρ hρ0 m)
        (expNeg_mul_le_pow a ρ ha hρ0 hρ m)
    exact CReal.leRat_smul_nonneg (hw0 m) hexp
  -- (2) the majorant's uniform term-ratio: f(m+1) ≤ (P·ρ)·f(m)
  have hdom : ∀ m, w (m + 1) * ρ ^ (m + 1) ≤ (P * ρ) * (w m * ρ ^ m) := by
    intro m
    rw [Q'.pow_succ]
    -- w(m+1)·(ρ·ρ^m) ≤ (P·w m)·(ρ·ρ^m) ≃ (P·ρ)·(w m·ρ^m)
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ (ρ * ρ ^ m) (hwratio m)
        (Q'.mul_nonneg ρ (ρ ^ m) hρ0 (Q'.pow_nonneg ρ hρ0 m))) ?_
    exact Q'.le_of_eqv (mul_mul_swap_eqv P (w m) ρ (ρ ^ m))
  -- (3) f(0) ≤ w 0  (f 0 = w 0 · ρ^0 = w 0 · 1 ≃ w 0)
  have hf0 : w 0 * ρ ^ 0 ≤ w 0 := by
    rw [Q'.pow_zero]; exact Q'.le_of_eqv (Q'.mul_one_eqv (w 0))
  -- assemble: Σ char ≤ Σ f ≤ H
  refine CReal.leRat_mono
    (CReal.leRat_csum _ (fun m => w m * ρ ^ m) hterm N) ?_
  exact geom_series_le (fun m => w m * ρ ^ m) (w 0) (P * ρ) H
    (Q'.mul_nonneg P ρ hP0 hρ0) hH hf0 hdom hrec N

/-! ## The SU(N) polynomial weight ratio `P = 4^q`

For the SU(N) per-axis weight `w(m) = (m+1)^{2q}`, the ratio constant is
`P = 4^q`: `(m+2)^{2q} ≤ 4^q·(m+1)^{2q}` because `m+2 ≤ 2(m+1)` and
`(2(m+1))^{2q} = 2^{2q}(m+1)^{2q} = 4^q(m+1)^{2q}`.  This discharges the
`hwratio` hypothesis of `charTail_geom_le` for the SU(N) axes. -/

/-- **The SU(N) polynomial-weight ratio (Nat).**  `(m+2)^{2q} ≤ 4^q·(m+1)^{2q}`. -/
theorem polyWeight_ratio_nat (q m : Nat) :
    (m + 2) ^ (2 * q) ≤ 4 ^ q * (m + 1) ^ (2 * q) := by
  calc (m + 2) ^ (2 * q)
      ≤ (2 * (m + 1)) ^ (2 * q) := Nat.pow_le_pow_left (by omega) (2 * q)
    _ = 2 ^ (2 * q) * (m + 1) ^ (2 * q) := by rw [Nat.mul_pow]
    _ = 4 ^ q * (m + 1) ^ (2 * q) := by
        rw [show (2 : Nat) ^ (2 * q) = 4 ^ q by rw [Nat.pow_mul]]

/-- **The SU(N) polynomial-weight ratio (`Q'`).**  For the weight
`w(m) = (m+1)^{2q}` (as `Q'`), `w(m+1) ≤ (4^q)·w(m)` — the `hwratio` input to
`charTail_geom_le`, so the SU(N) per-axis tail closes at `H = 1/(1 − 4^q·ρ)`
with `ρ = e^{−t h_i(1)}` and `4^q·ρ = b^{q} < 1`. -/
theorem polyWeight_ratio (q m : Nat) :
    Q'.ofNat ((m + 1 + 1) ^ (2 * q)) ≤ Q'.ofNat (4 ^ q) * Q'.ofNat ((m + 1) ^ (2 * q)) := by
  -- reduce to the Nat inequality through `ofNat` monotonicity + `ofNat_mul`
  show (Q'.ofNat ((m + 1 + 1) ^ (2 * q))).num * _
     ≤ (Q'.ofNat (4 ^ q) * Q'.ofNat ((m + 1) ^ (2 * q))).num * _
  have hnat : (m + 2) ^ (2 * q) ≤ 4 ^ q * (m + 1) ^ (2 * q) := polyWeight_ratio_nat q m
  have hln : (Q'.ofNat ((m + 1 + 1) ^ (2 * q))).num = (((m + 2) ^ (2 * q) : Nat) : Int) := rfl
  have hld : ((Q'.ofNat ((m + 1 + 1) ^ (2 * q))).den : Int) = 1 := rfl
  have hrn : (Q'.ofNat (4 ^ q) * Q'.ofNat ((m + 1) ^ (2 * q))).num
      = ((4 ^ q : Nat) : Int) * (((m + 1) ^ (2 * q) : Nat) : Int) := rfl
  have hrd : ((Q'.ofNat (4 ^ q) * Q'.ofNat ((m + 1) ^ (2 * q))).den : Int) = 1 := by
    rw [Q'.mul_den_cast]; rfl
  rw [hln, hld, hrn, hrd, Int.mul_one, Int.mul_one]
  -- goal: ↑((m+2)^{2q}) ≤ ↑(4^q) * ↑((m+1)^{2q})
  have : (((m + 2) ^ (2 * q) : Nat) : Int) ≤ (((4 ^ q) * ((m + 1) ^ (2 * q)) : Nat) : Int) := by
    exact_mod_cast hnat
  rw [Int.natCast_mul] at this
  exact this

end YMGap.RG

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RG.expNeg_poly_csum_le
#print axioms YMGap.RG.mul_mul_swap_eqv
#print axioms YMGap.RG.charTail_geom_le
#print axioms YMGap.RG.polyWeight_ratio_nat
#print axioms YMGap.RG.polyWeight_ratio
