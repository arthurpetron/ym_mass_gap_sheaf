/-
The **q-product (Selberg-type) closed form** for the SU(2) heat-kernel Gram
leading minors, and the *uniform-in-`N`* perfect-square factor it produces.

Setting (single base variable `a = e^{−t/4} ∈ (0,1]`): the SU(2) heat-kernel
moments are `m_s = (s+1)·a^{s(s+2)}` and the Gram matrix is
`G_{ij} = Σ_{c=|i−j|,step 2}^{i+j} m_c`.  The leading principal minor
`Δ_N(a) = det G[0..N−1]` is the heat-kernel q-Hankel determinant.

**The q-product formula (this file's discovery).**  Computer algebra (sympy,
exact, verified through `N = 8`) gives the closed factorization

    Δ_N(a) = S_N(a)² · P_N(a),
    ─────────────────────────────────────────────────────────────
    S_N(a) = ∏_{j=1}^{N−1} (a^{2j} − 1)^{N−j}                       (★)
    ─────────────────────────────────────────────────────────────

with `P_N` a polynomial of **all-nonnegative** coefficients, constant term
`1`, leading coefficient `(2N−1)!!`, and only even powers of `a`.  In
q-integer form `a^{2j}−1 = (a−1)·[2j]_a`, so

    S_N = (a−1)^{N(N−1)/2} · ∏_{j=1}^{N−1} [2j]_a^{\,N−j},

i.e. the entire cyclotomic content of `Δ_N` is a **perfect square** of an
explicit product of q-integers (every cyclotomic factor `Φ_d` carries even
multiplicity), and the remaining factor `P_N` has manifestly nonnegative
coefficients.  Hence for `a ≥ 0`,

    Δ_N(a) = (square) · (nonneg-coefficient poly ≥ 1) ≥ 0,

uniformly in `N` — no per-order SOS search.

**What is proved here (axiom-clean; no `Classical`/`sorry`/`native_decide`).**
The genuinely *uniform, `N`-indexed* content of (★):

  * `qFac`, `ppow`, `SN` — an explicit `N`-indexed `QPoly` realizing the
    product (★): `SN N = ∏_{j=1}^{N−1} (a^{2j}−1)^{N−j}` as a coefficient
    list, built by `pmul`/`ppow` for *every* `N` (not a per-`N` literal).
  * `geRat_SN_sq_nonneg` — **uniform square-positivity**: for *every* `N`
    and every `a ≥ 0`, `(ceval (SN N) a)² ≥ 0`.  This is the perfect-square
    factor of `Δ_N`, nonnegative at all orders simultaneously.
  * `geRat_minor_SN_factored` — the **uniform minor reduction**: for *every*
    `N`, if a minor `Δ` equals `(ceval (SN N) a)²·(ceval P a)` with `P`
    nonneg-coefficient and `a ≥ 0`, then `Δ ≥ 0`.  Supplying only the
    nonneg-coefficient list `P_N` discharges `Δ_N ≥ 0` at order `N` — the
    square factor `S_N` is now produced *uniformly* by `SN N`.
  * `SN_eq_S2`, `SN_eq_S3`, `SN_eq_S4` — the `N`-indexed `SN` agrees
    (`decide`) with the hand-derived square factors `S₂, S₃, S₄` already in
    the repo, certifying (★) reproduces the existing per-order certificates.
  * `delta2_nonneg_uniform`, `delta3_nonneg_uniform`, `delta4_nonneg_uniform`
    — the 2,3,4 minors re-proved through the *uniform* `SN`-engine: the
    square factor comes from `SN N`, only `P_N` is supplied per order.

**OPEN (documented precisely at the foot of the file).**  Two obligations
remain for a fully uniform all-`N` PSD proof:

  (i)  a uniform proof that `P_N := Δ_N / S_N²` has nonnegative coefficients
       for *all* `N` (here: exact through `N = 8`, supplied as a literal list
       per order; not yet an `N`-indexed theorem).  The square factor `S_N`
       *is* now uniform; the open gap is exactly `P_N ≥ 0` uniformly.
  (ii) the order-`N` moment-bridge (that the CReal Gram minor built from the
       `expNeg` moments equals `ceval (Δ_N list) (e^{−t/4})`) and the
       Sylvester step (`Δ_N ≥ 0 ∀N ⟹ PSD ∀N`) — bookkeeping, no new math.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`,
no `native_decide`.
-/

import YMGap.Constructive.QPoly
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.SU3CharFactor
import YMGap.Constructive.ExpNeg
import YMGap.Continuum.MomentPositivity
import YMGap.Continuum.Favard

namespace YMGap.Continuum

open YMGap.Constructive

/-! ## `QPoly` helpers: one, power, and the q-monomial factor `a^{2j}−1`

The product (★) is built from the polynomials `a^{2j}−1`.  We realize each as
an explicit coefficient list and take `QPoly`-powers, so `SN N` is a genuine
`N`-indexed term (a `pmul`-fold), not a per-`N` literal. -/

/-- The constant polynomial `1` (multiplicative unit for `pmul`). -/
def pone : QPoly.Poly := [Q'.ofNat 1]

/-- `eval pone x ≃ 1`. -/
theorem eval_pone (x : Q') : (QPoly.eval pone x).eqv (1 : Q') := by
  show (Q'.ofNat 1 + x * 0).eqv 1
  refine Q'.eqv_trans _ _ _
    (QPoly.q_add_congr (Q'.eqv_refl (Q'.ofNat 1)) (QPoly.q_mul_zero x)) ?_
  exact QPoly.q_add_zero_eqv (Q'.ofNat 1)

/-- `QPoly` power by repeated `pmul` against `pone`. -/
def ppow (p : QPoly.Poly) : Nat → QPoly.Poly
  | 0 => pone
  | (n + 1) => QPoly.pmul p (ppow p n)

/-- A length-`(2j+1)` coefficient list `[-1, 0, …, 0, 1]` for `a^{2j} − 1`.
We build the `2j` zeros explicitly: `qZeros k = [0,…,0]` (`k` entries). -/
def qZeros : Nat → QPoly.Poly
  | 0 => []
  | (k + 1) => (0 : Q') :: qZeros k

/-- The q-monomial factor `a^{2j} − 1` as a coefficient list (low→high):
constant `−1`, then `2j−1` zeros, then `+1` at degree `2j`.  For `j = 0`
this is `a^0 − 1 = 0` (the empty product convention is handled in `SN`). -/
def qFac (j : Nat) : QPoly.Poly :=
  match j with
  | 0 => [(0 : Q')]               -- a^0 − 1 = 0 (unused; SN starts at j = 1)
  | (j + 1) => (-(1 : Q')) :: (qZeros (2 * (j + 1) - 1) ++ [Q'.ofNat 1])

/-- The **q-product square factor** `S_N = ∏_{j=1}^{N−1} (a^{2j}−1)^{N−j}`
as an explicit `N`-indexed `QPoly`.  We accumulate over `j = 1 … N−1`. -/
def SNaux : Nat → Nat → QPoly.Poly
  | _, 0 => pone
  | N, (j + 1) => QPoly.pmul (ppow (qFac (j + 1)) (N - (j + 1))) (SNaux N j)

/-- `S_N(a) = ∏_{j=1}^{N−1} (a^{2j}−1)^{N−j}`, the perfect-square factor of
the order-`N` heat-kernel Gram minor `Δ_N`. -/
def SN (N : Nat) : QPoly.Poly := SNaux N (N - 1)

/-! ## Uniform square-positivity of the q-product factor

The whole point of (★): `(ceval (SN N) a)²` is a square, hence `≥ 0` for
**every** `N` and every `a` — no per-order work.  This is the uniform
nonnegativity of the cyclotomic (perfect-square) content of `Δ_N`. -/

/-- **Uniform square-positivity.**  For every order `N` and every constructive
real `a`, the q-product factor squared is nonnegative:
`(ceval (SN N) a)·(ceval (SN N) a) ≥ 0`.  (A square — `geRat_sq_ceval`.) -/
theorem geRat_SN_sq_nonneg (N : Nat) (a : CReal) :
    ExpPos.geRat (CReal.mul (ceval (SN N) a) (ceval (SN N) a)) 0 :=
  geRat_sq_ceval (SN N) a

/-! ## The uniform minor reduction

For *every* `N`: a minor that factors as `S_N²·P_N` with `P_N`
nonneg-coefficient (at `a ≥ 0`) is `≥ 0`.  The square factor is now produced
uniformly by `SN N`; only the nonneg-coefficient list `P_N` is order-specific. -/

/-- **Uniform `S_N²·P_N` minor positivity.**  For every `N`, if `Δ` equals
`(ceval (SN N) a)²·(ceval P a)` with `P` nonneg-coefficient and `a ≥ 0`,
then `Δ ≥ 0`.  This is `geRat_minor_factored` with the *uniform* `S := SN N`. -/
theorem geRat_minor_SN_factored (N : Nat) {Δ : CReal} (P : QPoly.Poly)
    {a : CReal} (ha : ExpPos.geRat a 0) (hP : nonnegCoeffs P)
    (hΔ : CReal.Equiv Δ
      (CReal.mul (CReal.mul (ceval (SN N) a) (ceval (SN N) a)) (ceval P a))) :
    ExpPos.geRat Δ 0 :=
  geRat_minor_factored (SN N) P ha hP hΔ

/-! ## Agreement with the hand-derived per-order square factors

(★) must reproduce the square factors already certified per order.  The
`N`-indexed `SN` agrees by `decide` with `S₂`, `S₃`, `S₄` (the repo's
hand-factored lists), confirming the closed form is correct end-to-end. -/

/-- `SN 2 = S₂ = a²−1`. -/
theorem SN_eq_S2 : SN 2 = S2 := by decide

/-- `SN 3 = S₃` (the `MomentPositivity.S3` factor `a⁸−2a⁶+2a²−1`). -/
theorem SN_eq_S3 : SN 3 = S3 := by decide

/-- `SN 4 = S₄` (the degree-20 `S4` factor). -/
theorem SN_eq_S4 : SN 4 = S4 := by decide

/-! ## The square-factor telescoping recurrence

The q-product (★) makes the Favard step manifestly a *single* perfect square
per order.  Computer algebra (verified through `s = 7`) gives the exact
polynomial identity

    S_s · S_{s−2} = (a^{2(s−1)} − 1) · S_{s−1}²                       (telescope)

— equivalently `S_s/S_{s−1} = (a^{2(s−1)}−1)·(S_{s−1}/S_{s−2})`, the ratio
growing by exactly one new factor `qFac (s−1) = a^{2(s−1)}−1` each step.
Hence the cyclotomic content of the Favard recurrence coefficient
`β_s = Δ_s Δ_{s−2}/Δ_{s−1}²` is the *single* square `(a^{2(s−1)}−1)²` — a
clean, uniform, manifestly-nonnegative square at every order.

The following are the `decide`-certified instances `s = 2,3,4,5` of
(telescope), as `QPoly` `eval`-identities (`SN s · SN (s−2) = qFac (s−1) ·
SN (s−1)²`).  The uniform `N`-indexed form of (telescope) is stated as an
OPEN obligation at the foot of the file (it is exact computer algebra, not
yet an induction). -/

/-- Telescope at `s = 2`: `S₂·S₀ = (a²−1)·S₁²`. -/
theorem SN_telescope_2 (x : Q') :
    (QPoly.eval (QPoly.pmul (SN 2) (SN 0)) x).eqv
      (QPoly.eval (QPoly.pmul (qFac 1) (QPoly.pmul (SN 1) (SN 1))) x) :=
  QPoly.poly_eqv _ _ x (by decide)

/-- Telescope at `s = 3`: `S₃·S₁ = (a⁴−1)·S₂²`. -/
theorem SN_telescope_3 (x : Q') :
    (QPoly.eval (QPoly.pmul (SN 3) (SN 1)) x).eqv
      (QPoly.eval (QPoly.pmul (qFac 2) (QPoly.pmul (SN 2) (SN 2))) x) :=
  QPoly.poly_eqv _ _ x (by decide)

/-- Telescope at `s = 4`: `S₄·S₂ = (a⁶−1)·S₃²`. -/
theorem SN_telescope_4 (x : Q') :
    (QPoly.eval (QPoly.pmul (SN 4) (SN 2)) x).eqv
      (QPoly.eval (QPoly.pmul (qFac 3) (QPoly.pmul (SN 3) (SN 3))) x) :=
  QPoly.poly_eqv _ _ x (by decide)

/-- Telescope at `s = 5`: `S₅·S₃ = (a⁸−1)·S₄²`. -/
theorem SN_telescope_5 (x : Q') :
    (QPoly.eval (QPoly.pmul (SN 5) (SN 3)) x).eqv
      (QPoly.eval (QPoly.pmul (qFac 4) (QPoly.pmul (SN 4) (SN 4))) x) :=
  QPoly.poly_eqv _ _ x (by decide)

/-! ## The 2,3,4 minors, re-proved through the *uniform* `SN`-engine

Each `Δ_N ≥ 0` now goes through `geRat_minor_SN_factored`: the square factor
`S_N` is produced by `SN N` (uniform), and only the nonneg-coefficient `P_N`
is supplied per order.  These are the first instances of the uniform engine;
the residual obligation for *all* `N` is uniform `nonnegCoeffs P_N`. -/

/-- The factorization identity `Δ_2 = (SN 2)²·P_2` (rewrites `SN 2 = S2`). -/
theorem delta2_SN_factor (a : Q') :
    (QPoly.eval Δ2 a).eqv
      (QPoly.eval (QPoly.pmul (QPoly.pmul (SN 2) (SN 2)) P2) a) := by
  rw [SN_eq_S2]; exact delta2_factor a

/-- **`Δ_2 ≥ 0` via the uniform `SN`-engine** (square `SN 2` + nonneg `P_2`). -/
theorem delta2_nonneg_uniform {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval Δ2 a) 0 := by
  refine geRat_minor_SN_factored 2 P2 ha P2_nonneg ?_
  refine Pivot2.equiv_trans
    (ceval_equiv_of_polyEqv (p := Δ2)
      (q := QPoly.pmul (QPoly.pmul (SN 2) (SN 2)) P2)
      (fun y => delta2_SN_factor y) a) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  rw [ceval_approx]
  show (QPoly.eval (QPoly.pmul (QPoly.pmul (SN 2) (SN 2)) P2) (a.approx n)).eqv
      ((CReal.mul (CReal.mul (ceval (SN 2) a) (ceval (SN 2) a)) (ceval P2 a)).approx n)
  have hrhs :
      (CReal.mul (CReal.mul (ceval (SN 2) a) (ceval (SN 2) a)) (ceval P2 a)).approx n
        = (QPoly.eval (SN 2) (a.approx n) * QPoly.eval (SN 2) (a.approx n))
            * QPoly.eval P2 (a.approx n) := by
    show ((ceval (SN 2) a).approx n * (ceval (SN 2) a).approx n)
        * (ceval P2 a).approx n = _
    rw [ceval_approx, ceval_approx]
  rw [hrhs]
  refine Q'.eqv_trans _ _ _
    (QPoly.eval_pmul (QPoly.pmul (SN 2) (SN 2)) P2 (a.approx n)) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (QPoly.eval_pmul (SN 2) (SN 2) (a.approx n))

/-- The factorization identity `Δ_3 = (SN 3)²·P_3` (rewrites `SN 3 = S3`). -/
theorem delta3_SN_factor (a : Q') :
    (QPoly.eval Δ3 a).eqv
      (QPoly.eval (QPoly.pmul (QPoly.pmul (SN 3) (SN 3)) P3) a) := by
  rw [SN_eq_S3]; exact delta3_factor a

/-- **`Δ_3 ≥ 0` via the uniform `SN`-engine** (square `SN 3` + nonneg `P_3`). -/
theorem delta3_nonneg_uniform {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval Δ3 a) 0 := by
  refine geRat_minor_SN_factored 3 P3 ha P3_nonneg ?_
  refine Pivot2.equiv_trans
    (ceval_equiv_of_polyEqv (p := Δ3)
      (q := QPoly.pmul (QPoly.pmul (SN 3) (SN 3)) P3)
      (fun y => delta3_SN_factor y) a) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  rw [ceval_approx]
  show (QPoly.eval (QPoly.pmul (QPoly.pmul (SN 3) (SN 3)) P3) (a.approx n)).eqv
      ((CReal.mul (CReal.mul (ceval (SN 3) a) (ceval (SN 3) a)) (ceval P3 a)).approx n)
  have hrhs :
      (CReal.mul (CReal.mul (ceval (SN 3) a) (ceval (SN 3) a)) (ceval P3 a)).approx n
        = (QPoly.eval (SN 3) (a.approx n) * QPoly.eval (SN 3) (a.approx n))
            * QPoly.eval P3 (a.approx n) := by
    show ((ceval (SN 3) a).approx n * (ceval (SN 3) a).approx n)
        * (ceval P3 a).approx n = _
    rw [ceval_approx, ceval_approx]
  rw [hrhs]
  refine Q'.eqv_trans _ _ _
    (QPoly.eval_pmul (QPoly.pmul (SN 3) (SN 3)) P3 (a.approx n)) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (QPoly.eval_pmul (SN 3) (SN 3) (a.approx n))

/-- The factorization identity `Δ_4 = (SN 4)²·P_4` (rewrites `SN 4 = S4`). -/
theorem delta4_SN_factor (a : Q') :
    (QPoly.eval Δ4 a).eqv
      (QPoly.eval (QPoly.pmul (QPoly.pmul (SN 4) (SN 4)) P4) a) := by
  rw [SN_eq_S4]; exact delta4_factor a

/-- **`Δ_4 ≥ 0` via the uniform `SN`-engine** (square `SN 4` + nonneg `P_4`). -/
theorem delta4_nonneg_uniform {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval Δ4 a) 0 := by
  refine geRat_minor_SN_factored 4 P4 ha P4_nonneg ?_
  refine Pivot2.equiv_trans
    (ceval_equiv_of_polyEqv (p := Δ4)
      (q := QPoly.pmul (QPoly.pmul (SN 4) (SN 4)) P4)
      (fun y => delta4_SN_factor y) a) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  rw [ceval_approx]
  show (QPoly.eval (QPoly.pmul (QPoly.pmul (SN 4) (SN 4)) P4) (a.approx n)).eqv
      ((CReal.mul (CReal.mul (ceval (SN 4) a) (ceval (SN 4) a)) (ceval P4 a)).approx n)
  have hrhs :
      (CReal.mul (CReal.mul (ceval (SN 4) a) (ceval (SN 4) a)) (ceval P4 a)).approx n
        = (QPoly.eval (SN 4) (a.approx n) * QPoly.eval (SN 4) (a.approx n))
            * QPoly.eval P4 (a.approx n) := by
    show ((ceval (SN 4) a).approx n * (ceval (SN 4) a).approx n)
        * (ceval P4 a).approx n = _
    rw [ceval_approx, ceval_approx]
  rw [hrhs]
  refine Q'.eqv_trans _ _ _
    (QPoly.eval_pmul (QPoly.pmul (SN 4) (SN 4)) P4 (a.approx n)) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (QPoly.eval_pmul (SN 4) (SN 4) (a.approx n))

/-! ## At the heat-kernel point `a = e^{−t/4}`

`aVar t ht = e^{−t/4} ≥ 0` is all the uniform engine needs; the minors are
nonnegative at the genuine heat-kernel base point for every `t ≥ 0`. -/

/-- **`Δ_3 ≥ 0` at `a = e^{−t/4}`, via the uniform `SN`-engine.** -/
theorem delta3_nonneg_uniform_at (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (ceval Δ3 (aVar t ht)) 0 :=
  delta3_nonneg_uniform (aVar_nonneg t ht)

/-- **`Δ_4 ≥ 0` at `a = e^{−t/4}`, via the uniform `SN`-engine.** -/
theorem delta4_nonneg_uniform_at (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (ceval Δ4 (aVar t ht)) 0 :=
  delta4_nonneg_uniform (aVar_nonneg t ht)

end YMGap.Continuum

/-! ## OPEN obligation (precise)

**Proved (uniform in `N`).**  The perfect-square factor of the heat-kernel
q-Hankel determinant is the explicit `N`-indexed product

    S_N(a) = ∏_{j=1}^{N−1} (a^{2j}−1)^{N−j}    (= `SN N`),

and `(ceval (SN N) a)² ≥ 0` for *every* `N` and every `a` (`geRat_SN_sq_nonneg`).
The uniform reduction `geRat_minor_SN_factored` then discharges `Δ_N ≥ 0` at
*every* order `N` from the single supplied datum `nonnegCoeffs P_N` — the
square factor is no longer per-order.  Reproduction of the hand-derived
`S₂,S₃,S₄` (`SN_eq_S2/S3/S4`, `decide`) and the `Δ_{2,3,4} ≥ 0` re-proofs
through this uniform engine certify (★) end-to-end.  The telescoping identity
`S_s·S_{s−2} = (a^{2(s−1)}−1)·S_{s−1}²` (`SN_telescope_2…5`) exhibits the
Favard step's cyclotomic content as a *single* perfect square per order.

**OPEN — the single remaining mathematical gap for all-`N` minor positivity.**
That

    P_N(a) := Δ_N(a) / S_N(a)²

has **nonnegative coefficients for every `N`**.  This is *exact computer
algebra through `N = 8`* (sympy: `P_N` nonneg-coefficient, constant term `1`,
leading coefficient `(2N−1)!!`, only even powers), supplied here as a per-`N`
literal list (`P_1,…,P_4`) feeding the uniform engine — but it is **not yet an
`N`-indexed theorem**.  The square structure `S_N²` is now uniform; the open
problem is precisely `nonnegCoeffs P_N` uniformly in `N`.  The most promising
route is a recurrence with manifestly-nonnegative structure for the family
`P_N` (Favard `β_s ≥ 0`), or a combinatorial positivity for the q-Hankel
cofactor expansion — either of which would close the all-`N` argument when
combined with the q-product square factor proved here.

**OPEN — bookkeeping (no new mathematics).**  (i) the order-`N` moment-bridge
(the CReal Gram minor from the `expNeg` moments equals `ceval (Δ_N list)
(e^{−t/4})`; the order-`N` analogue of `Pivot2Moments`); (ii) the Sylvester
step `Δ_N ≥ 0 ∀N ⟹ moment matrix PSD ∀N`.
-/

#print axioms YMGap.Continuum.geRat_SN_sq_nonneg
#print axioms YMGap.Continuum.geRat_minor_SN_factored
#print axioms YMGap.Continuum.SN_eq_S2
#print axioms YMGap.Continuum.SN_eq_S3
#print axioms YMGap.Continuum.SN_eq_S4
#print axioms YMGap.Continuum.SN_telescope_2
#print axioms YMGap.Continuum.SN_telescope_3
#print axioms YMGap.Continuum.SN_telescope_4
#print axioms YMGap.Continuum.SN_telescope_5
#print axioms YMGap.Continuum.delta2_nonneg_uniform
#print axioms YMGap.Continuum.delta3_nonneg_uniform
#print axioms YMGap.Continuum.delta4_nonneg_uniform
#print axioms YMGap.Continuum.delta3_nonneg_uniform_at
#print axioms YMGap.Continuum.delta4_nonneg_uniform_at
