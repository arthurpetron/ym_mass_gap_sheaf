/-
Research frontier — the **uniform-in-N** SU(2) heat-kernel Gram positivity.

The heat-kernel moments are `m_s = (s+1)·a^{s(s+2)}` in the single base
variable `a = e^{−t/4} ∈ (0,1]` (every moment a *monomial* in `a`; the
exponent `s(s+2) = (s+1)²−1` is even-shifted Gaussian/theta data).  The
SU(2) Gram matrix `G_{ij} = ⟨χ_iχ_j⟩_t = Σ_c N^c_{ij} m_c` must be
positive-semidefinite for **all** sizes `N` simultaneously.

This file isolates the *uniform structural engine* discovered by factoring
the leading principal minors `Δ_N(a) = det G[0..N−1]`:

  Δ_1 = 1
  Δ_2 = (a−1)²(a+1)²·(3a⁴+2a²+1)
  Δ_3 = (a−1)⁶(a+1)⁶(a²+1)²·(15a¹⁶+24a¹⁴+…+4a²+1)
  Δ_4 = (a−1)¹²(a+1)¹²(a²+1)⁴(a²−a+1)²(a²+a+1)²·(105a⁴⁰+…+1)
  …

**Every** leading minor factors uniformly as

    Δ_N(a)  =  S_N(a)² · P_N(a),

where `S_N` collects the *even-multiplicity* cyclotomic factors (so `S_N²`
is a perfect square, `≥ 0` for free) and `P_N` is a polynomial in `a` with
**all-nonnegative coefficients** and only even exponents (a positive
combination of monomials in `a²`, with constant term `1`).  For `a ≥ 0`
both factors are manifestly `≥ 0`, so `Δ_N(a) ≥ 0` — uniformly in `N`, with
**no** per-N SOS search: the certificate is just (a square)·(positive
coefficients).  By Sylvester this is exactly the all-N PSD content.

What is proved here (axiom-clean, no `Classical`/`sorry`):

  * `ceval` — Horner evaluation of a rational-coefficient `QPoly` at a
    `CReal`, and its `eval`-on-`approx` law.
  * `geRat_ceval_of_nonnegCoeffs` — the **positivity engine**: a poly with
    all-nonneg coefficients, evaluated at `a ≥ 0`, is `≥ 0`.  (Horner
    induction; the reusable core that works at every order `N`.)
  * `geRat_sq_ceval`, `geRat_minor_factored` — a square times a
    nonneg-coefficient poly is `≥ 0`: the shape of every `Δ_N`.
  * `delta3_factor`  — the **concrete N = 3 certificate**:
    `Δ_3(a) = S_3(a)²·P_3(a)` as a `QPoly` `decide`-identity, with `P_3`
    nonneg-coefficient (`decide`), hence
  * `delta3_nonneg` — `Δ_3(e^{−t/4}) ≥ 0`, the 3×3 leading Gram minor,
    proved purely from the factorization + the engine (no hand SOS).

The OPEN obligation (documented at the foot of the file) is the
**moment-bridge**: that the *actual* CReal Gram minor built from the
`expNeg` moments equals `ceval (Δ_N coefficient list) (e^{−t/4})` — the
order-N analogue of `Pivot2Moments`, a mechanical exponent-folding, not a
new mathematical idea.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Constructive.QPoly
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.SU3CharFactor
import YMGap.Constructive.ExpNeg
import YMGap.Constructive.Soundness
import YMGap.Continuum.Pivot2Moments

namespace YMGap.Continuum

open YMGap.Constructive

/-! ## CReal Horner evaluation of a rational-coefficient polynomial

`QPoly.eval` lives over `Q'`; the Gram entries are `CReal`s (the `expNeg`
moments).  We evaluate the *same* coefficient lists at a `CReal` point by
Horner recursion through `CReal.add`/`CReal.mul`/`CReal.ofQ'`.  Because each
constructor acts **approx-wise**, `(ceval p x).approx n = QPoly.eval p (x.approx n)`
*definitionally* — the bridge to the `Q'` ring lemmas (`QPoly.poly_eqv`). -/

/-- Horner evaluation `[c₀,c₁,…] ↦ c₀ + x·(c₁ + x·(…))` of a rational
coefficient list at a constructive real `x`. -/
def ceval : QPoly.Poly → CReal → CReal
  | [], _ => CReal.czero
  | (c :: cs), x => CReal.add (CReal.ofQ' c) (CReal.mul x (ceval cs x))

/-- `(ceval p x).approx n` is the `Q'`-Horner `QPoly.eval p (x.approx n)`. -/
theorem ceval_approx (p : QPoly.Poly) (x : CReal) (n : Nat) :
    (ceval p x).approx n = QPoly.eval p (x.approx n) := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
      show c + x.approx n * (ceval cs x).approx n
          = c + x.approx n * QPoly.eval cs (x.approx n)
      rw [ih]

/-- `ceval` of `≃`-equal coefficient lists agree as `CReal`s — the lift of
`QPoly.poly_eqv` to the constructive-real point. -/
theorem ceval_equiv_of_polyEqv {p q : QPoly.Poly}
    (h : ∀ y : Q', (QPoly.eval p y).eqv (QPoly.eval q y)) (x : CReal) :
    CReal.Equiv (ceval p x) (ceval q x) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => by
    rw [ceval_approx, ceval_approx]; exact h (x.approx n))

/-! ## The positivity engine: nonneg-coefficient polynomials at `a ≥ 0`

A coefficient list is *nonnegative* when every entry is `≥ 0` (a `Bool`
test, so `Decidable` for free).  Horner then keeps a running value `≥ 0`:
`c + a·(rest)` with `c ≥ 0`, `a ≥ 0`, `rest ≥ 0`.  This is the uniform core
— every `P_N` (the positive factor of `Δ_N`) satisfies it. -/

/-- Every coefficient `≥ 0`, as a `Bool` (so `Decidable` is free). -/
def nonnegCoeffsB : QPoly.Poly → Bool
  | [] => true
  | (c :: cs) => decide ((0 : Q') ≤ c) && nonnegCoeffsB cs

def nonnegCoeffs (p : QPoly.Poly) : Prop := nonnegCoeffsB p = true

instance (p : QPoly.Poly) : Decidable (nonnegCoeffs p) :=
  inferInstanceAs (Decidable (_ = true))

/-- **Positivity engine.**  A polynomial with all-nonnegative coefficients,
evaluated at a constructive real `x ≥ 0`, is `≥ 0`.  Horner induction:
`ceval (c::cs) x = c + x·(ceval cs x)`, a sum of `c ≥ 0` and a product of
two nonnegatives. -/
theorem geRat_ceval_of_nonnegCoeffs :
    ∀ (p : QPoly.Poly) {x : CReal}, ExpPos.geRat x 0 → nonnegCoeffs p →
      ExpPos.geRat (ceval p x) 0
  | [], _, _, _ => SumOfSquares.geRat_czero
  | (c :: cs), x, hx, h => by
      have hb : decide ((0 : Q') ≤ c) = true ∧ nonnegCoeffsB cs = true := by
        have h' := h
        rw [nonnegCoeffs, nonnegCoeffsB, Bool.and_eq_true] at h'
        exact h'
      have hc : (0 : Q') ≤ c := of_decide_eq_true hb.1
      have hcs : ExpPos.geRat (ceval cs x) 0 :=
        geRat_ceval_of_nonnegCoeffs cs hx hb.2
      have hprod : ExpPos.geRat (CReal.mul x (ceval cs x)) 0 :=
        CReal.mul_nonneg hx hcs
      have hsum : ExpPos.geRat (CReal.add (CReal.ofQ' c) (CReal.mul x (ceval cs x)))
          ((0 : Q') + 0) :=
        SumOfSquares.geRat_add (SumOfSquares.geRat_ofQ'_nonneg hc) hprod
      exact ExpPos.geRat_mono hsum (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_add_zero_eqv 0)))

/-! ## The universal minor shape: `Δ_N = S_N² · P_N`

A perfect square is `≥ 0` for free; times a nonneg-coefficient polynomial
(at `a ≥ 0`) it stays `≥ 0`.  This is the *shape* every leading minor has;
`delta3_nonneg` below is the first concrete instance. -/

/-- A square `(ceval S x)²` is nonnegative. -/
theorem geRat_sq_ceval (S : QPoly.Poly) (x : CReal) :
    ExpPos.geRat (CReal.mul (ceval S x) (ceval S x)) 0 :=
  SumOfSquares.geRat_sq_nonneg (ceval S x)

/-- **Universal minor positivity (factored form).**  If a minor equals
`S(x)²·P(x)` with `P` nonneg-coefficient and `x ≥ 0`, it is `≥ 0`. -/
theorem geRat_minor_factored {Δ : CReal} (S P : QPoly.Poly) {x : CReal}
    (hx : ExpPos.geRat x 0) (hP : nonnegCoeffs P)
    (hΔ : CReal.Equiv Δ (CReal.mul (CReal.mul (ceval S x) (ceval S x)) (ceval P x))) :
    ExpPos.geRat Δ 0 :=
  SU3CharFactor.geRat_of_equiv hΔ
    (CReal.mul_nonneg (geRat_sq_ceval S x) (geRat_ceval_of_nonnegCoeffs P hx hP))

/-! ## Concrete certificate: the 3×3 leading Gram minor

`Δ_3(a) = S_3(a)²·P_3(a)` with (coefficients low→high)

  S_3 = a⁸ − 2a⁶ + 2a² − 1     ( = (a−1)³(a+1)³(a²+1) )
  P_3 = 1 + 4a² + 12a⁴ + 20a⁶ + 32a⁸ + 36a¹⁰ + 36a¹² + 24a¹⁴ + 15a¹⁶

and `Δ_3` expanded is the degree-32 list below.  Both the factorization and
`nonnegCoeffs P_3` are pure `decide`s on `Q'` coefficient lists. -/

/-- `S_3` coefficient list (low→high): `a⁸ − 2a⁶ + 2a² − 1`. -/
def S3 : QPoly.Poly :=
  [-(1 : Q'), 0, Q'.ofNat 2, 0, 0, 0, -(Q'.ofNat 2), 0, Q'.ofNat 1]

/-- `P_3` coefficient list (low→high), all nonnegative, even exponents. -/
def P3 : QPoly.Poly :=
  [Q'.ofNat 1, 0, Q'.ofNat 4, 0, Q'.ofNat 12, 0, Q'.ofNat 20, 0, Q'.ofNat 32,
   0, Q'.ofNat 36, 0, Q'.ofNat 36, 0, Q'.ofNat 24, 0, Q'.ofNat 15]

/-- `Δ_3` coefficient list (low→high): the expanded degree-32 minor. -/
def Δ3 : QPoly.Poly :=
  [Q'.ofNat 1, 0, 0, 0, 0, 0, -(Q'.ofNat 8), 0, Q'.ofNat 6, 0, 0, 0, 0, 0,
   Q'.ofNat 12, 0, 0, 0, -(Q'.ofNat 16), 0, 0, 0, 0, 0, -(Q'.ofNat 22), 0,
   Q'.ofNat 48, 0, 0, 0, -(Q'.ofNat 36), 0, Q'.ofNat 15]

/-- `P_3` has all-nonnegative coefficients (`decide`). -/
theorem P3_nonneg : nonnegCoeffs P3 := by decide

/-- **The N = 3 factorization identity** `Δ_3 = S_3²·P_3`, as a `QPoly`
`decide`-certificate: every coefficient of `psub Δ3 (pmul (pmul S3 S3) P3)`
is `≃ 0`. -/
theorem delta3_factor (a : Q') :
    (QPoly.eval Δ3 a).eqv (QPoly.eval (QPoly.pmul (QPoly.pmul S3 S3) P3) a) :=
  QPoly.poly_eqv _ _ a (by decide)

/-- **The 3×3 leading Gram minor is nonnegative**, *as a polynomial in*
`a = e^{−t/4}`: for any constructive real `a ≥ 0`,
`ceval Δ3 a = ceval S3 a · ceval S3 a · ceval P3 a ≥ 0` — a square times a
nonneg-coefficient polynomial.  No per-order SOS search: the certificate is
the uniform `Δ_N = S_N²·P_N` shape. -/
theorem delta3_nonneg {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval Δ3 a) 0 := by
  refine geRat_minor_factored S3 P3 ha P3_nonneg ?_
  -- ceval Δ3 a ≃ ceval (pmul (pmul S3 S3) P3) a  (by the QPoly identity),
  -- and the RHS ≃ (ceval S3 a · ceval S3 a) · ceval P3 a  (ceval ∘ pmul).
  refine Pivot2.equiv_trans
    (ceval_equiv_of_polyEqv (p := Δ3) (q := QPoly.pmul (QPoly.pmul S3 S3) P3)
      (fun y => delta3_factor y) a) ?_
  -- pmul law on `ceval`, pushed through `approx` to the `Q'` `eval_pmul`.
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  rw [ceval_approx]
  show (QPoly.eval (QPoly.pmul (QPoly.pmul S3 S3) P3) (a.approx n)).eqv
      ((CReal.mul (CReal.mul (ceval S3 a) (ceval S3 a)) (ceval P3 a)).approx n)
  -- RHS approx = (eval S3 · eval S3) · eval P3  (each ceval acts approx-wise)
  have hrhs :
      (CReal.mul (CReal.mul (ceval S3 a) (ceval S3 a)) (ceval P3 a)).approx n
        = (QPoly.eval S3 (a.approx n) * QPoly.eval S3 (a.approx n))
            * QPoly.eval P3 (a.approx n) := by
    show ((ceval S3 a).approx n * (ceval S3 a).approx n) * (ceval P3 a).approx n
        = _
    rw [ceval_approx, ceval_approx]
  rw [hrhs]
  -- eval (pmul (pmul S3 S3) P3) y ≃ (eval S3 y · eval S3 y) · eval P3 y
  refine Q'.eqv_trans _ _ _
    (QPoly.eval_pmul (QPoly.pmul S3 S3) P3 (a.approx n)) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (QPoly.eval_pmul S3 S3 (a.approx n))

/-! ## The base point `a = e^{−t/4} ≥ 0`

The uniform variable.  `a ≥ 0` is all the engine needs, so the 3×3 minor
nonnegativity holds at the genuine heat-kernel point. -/

/-- `a = e^{−t/4}` (the uniform base variable; `t ≥ 0`). -/
def aVar (t : Q') (ht : (0 : Q') ≤ t) : CReal :=
  ExpNeg.expNeg (t * Q'.mkPos 1 4 (by decide)) (Q'.mul_nonneg t _ ht (by decide))

theorem aVar_nonneg (t : Q') (ht : (0 : Q') ≤ t) : ExpPos.geRat (aVar t ht) 0 :=
  expNeg_geRat_zero _ _

/-- **The 3×3 leading Gram minor, evaluated at the heat-kernel point
`a = e^{−t/4}`, is nonnegative** — the polynomial-level 3×3 Sylvester
positivity, for every `t ≥ 0`, via the uniform `Δ_N = S_N²·P_N` shape. -/
theorem delta3_nonneg_at (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (ceval Δ3 (aVar t ht)) 0 :=
  delta3_nonneg (aVar_nonneg t ht)

end YMGap.Continuum

/-! ## OPEN obligation (the order-N moment-bridge)

What is **proved** above is the *uniform positivity engine* and its
realization at `N = 3` purely as a statement about the polynomial `Δ_3(a)`:

  for every `a ≥ 0`,  `ceval Δ3 a = (ceval S3 a)²·(ceval P3 a) ≥ 0`,

with `S3`, `P3` fixed integer-coefficient lists and `P3` nonneg-coefficient
— both discharged by `decide`.  Combined with the structural discovery
(verified by exact factorization through `N = 6`)

    Δ_N(a)  =  S_N(a)² · P_N(a),   P_N nonneg-coefficient, S_N a polynomial,

the engine `geRat_minor_factored` gives `Δ_N ≥ 0` for **every** `N` as soon
as the two lists `(S_N, P_N)` are supplied — no per-N SOS search.

**OPEN.**  The remaining obligation is the *moment-bridge*: that the actual
constructive-real leading minor

    Δ_N^CReal(t) := det (G_{ij})_{0≤i,j<N},  G_{ij} = Σ_c N^c_{ij}·m_c(t),
    m_s(t) = (s+1)·expNeg(t·s(s+2)/4),

equals `ceval (Δ_N coefficient list) (e^{−t/4})` as a `CReal`.  At `N = 2`
this is exactly `Pivot2Moments.pivotGram_eqv_poly` (there the variable was
`r = e^{−t/2} = a²`; in the present uniform `a`-variable the same identity
reads `Δ_2(a) = (a−1)²(a+1)²(3a⁴+2a²+1)`).  For general `N` it is a *purely
mechanical* exponent-folding — each `m_s` is `(s+1)·a^{s(s+2)}`, folded
through `expNeg_add_equiv` exactly as in `Pivot2Moments` — together with
expanding the determinant.  No new mathematical content; the obstruction is
only the volume of `expNeg`-folding and determinant bookkeeping.

**Two further uniform-closure obligations** (the genuinely open mathematics,
beyond bookkeeping):

  (i)  a *uniform* construction of the lists `(S_N, P_N)` — i.e. a proof
       that the factorization `Δ_N = S_N²·P_N` holds for all `N` with `P_N`
       nonneg-coefficient (here verified by exact computer algebra through
       `N = 6`, not yet proved as an `N`-indexed theorem).  The cleanest
       route is the **three-term recurrence / Favard** form: the monic
       orthogonal polynomials of the heat-kernel moment functional satisfy
       `P_{s+1} = (x−α_s)P_s − β_s P_{s−1}`, and PSD ⟺ `β_s(a) ≥ 0` for all
       `s`; a closed form or monotone structure for `β_s(a)` would replace
       the per-N lists by a single uniform inequality.

  (ii) the Sylvester step `(Δ_N ≥ 0 ∀N) ⟹ PSD ∀N`, standard for
       Hankel/Gram matrices but not yet formalized in this repo.

The most promising direction is therefore **direction 2 made uniform**: the
`Δ_N = S_N²·P_N` decomposition is *empirically exact and uniform in N*
(square × all-positive-coefficient), which is a far stronger and cleaner
structure than a generic per-N SOS certificate; closing (i) — most likely
via the `β_s ≥ 0` recurrence — would finish the all-N argument.
-/

#print axioms YMGap.Continuum.geRat_ceval_of_nonnegCoeffs
#print axioms YMGap.Continuum.geRat_minor_factored
#print axioms YMGap.Continuum.P3_nonneg
#print axioms YMGap.Continuum.delta3_factor
#print axioms YMGap.Continuum.delta3_nonneg
#print axioms YMGap.Continuum.delta3_nonneg_at
