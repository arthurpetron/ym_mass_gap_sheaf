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
import YMGap.RG.CharacterTailAntitone
import YMGap.RG.PolylogTail

namespace YMGap.RG

open YMGap.Constructive

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

end YMGap.RG

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RG.expNeg_poly_csum_le
