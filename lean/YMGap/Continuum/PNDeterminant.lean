/-
Wall-1 (algebraic positivity kernel) — a focused extension of the
**column-coefficient** uniform fragment of `nonnegCoeffs P_N`, with an honest
account of why the two live research routes (a sign-clean symplectic / LGV
determinant model, and a Dodgson–Toda induction) do **not** close it.

Setup (same uniform base variable as `MomentPositivity`/`Favard`/`LGVPositivity`):
`a = e^{−t/4} ∈ (0,1]`, moments `m_s = (s+1)·a^{s(s+2)}`, leading Gram minors
`Δ_N(a) = det G[0..N−1]`, uniform factorization `Δ_N = S_N²·P_N` with `S_N`
the explicit q-product and `P_N` (empirically) nonneg-coefficient, `P_N(0)=1`,
leading `(2N−1)!!`, only even powers of `a`.  Writing `P_N(a)=Σ_j c_j(N)·a^{2j}`,
the lowest columns `c_j(N)` (fixed `j`, varying `N`) are exact polynomials in
`N` of degree `j` with leading coefficient `2ʲ/j!`.

`LGVPositivity.lean` proves the four lowest column nonnegativities as genuine
`∀N` theorems (`c_0,…,c_3`).  This file adds the **next** reliable column,

    c_4(N) = (4N⁴ + 20N³ − 97N² + 73N − 30)/6,

certified nonnegative for every `N ≥ 4` (a genuine `∀N` theorem over `Q'`, not
a per-`N` `decide`), and ties it to the actual `P_4` coefficient.  This closed
form is exact computer-algebra verified against the genuine residual
coefficients `c_4(N)` for `N = 4,…,9` (the determinant `Δ_N` and the residual
`P_N = Δ_N/S_N²` recomputed from scratch; the fitted leading coefficient
`2⁴/4! = 2/3` matches the theoretical column-leading law).

# Why this is a *fragment*, not a closer (the honest Wall-1 verdict)

The column-polynomial phenomenon is **uniform only on the low-q strip**.  Two
structural obstructions, both established by exact computer algebra and
unchanged by this pass:

  1. **Conditional positivity / growing thresholds.**  Each `c_j(N)` equals its
     degree-`j` polynomial only in the *interior regime* `N ≳ j` (the threshold
     where `a^{2j}` enters the low part of `P_N`); below it the same polynomial
     takes negative values (`c_2(1)=−2`, `c_3(1)=−4`, `c_4` first matches only at
     `N=4`).  A uniform certificate needs, for each `j`, the closed form *and*
     its validity threshold, and the thresholds grow with `j`.

  2. **`Θ(N³)` columns, with the bulk unreachable.**  `deg_q P_N = N(N²−1)/3`,
     so `P_N` has order `N³` nonzero coefficients.  For fixed `N` the bulk
     coefficients sit at `k ∼ N³`, deep in the *boundary* region where the
     polynomial-in-`N` description does not apply.  Concretely, with symbolic
     `Δ_N` feasible only through `N = 9`, columns `k ≥ 5` are **not even pinned**
     by the data: the fitted leading coefficient of column `5` (`1/4`) already
     disagrees with the theoretical `2⁵/5! = 4/15`, i.e. column `5` has not yet
     entered its interior regime in the available window.

# The two research routes (both ruled out as self-contained closers)

  * **Symplectic / LGV determinant model.**  The Gram is exactly the
    Hankel−minus−Toeplitz `G_{ij}=h_{i+j}−h_{|i−j|−2}` symplectic signature, and
    `a·G` is a nonneg-coefficient matrix of theta-monomials `t_r=r·a^{r²}`, so
    *all* sign content of `Δ_N` is the determinantal cancellation of a
    nonneg-coefficient matrix.  But: (i) `P_N` is **not** a nonneg combination of
    principal Schur/symplectic specializations — an exact Farkas certificate
    rules this out already at `N=2`; (ii) the naive LGV / coefficient-total-
    nonnegativity fails — the `5×5` `a·G` has 226 sign-mixed minors (smallest a
    `2×2`: `3a¹⁰−4a⁸+a²`); (iii) the staircase sequence `h_n` is **not** a
    positive (Hamburger) moment sequence (`det[h_{i+j}]` is sign-mixed at `N=2`),
    so the symplectic-Schur positivity theorems do not apply.  The only surviving
    sub-route is a **non-principal** (charge / major-index) vicious-walker path
    sum, which was not constructed.

  * **Dodgson–Toda induction.**  The exact relation is
    `β_k = (q^k−1)²·P_{k+1}P_{k−1}/P_k²` (verified `k≤7`), i.e. the Favard
    coefficient `β_k=Δ_{k+1}Δ_{k−1}/Δ_k²` has denominator *exactly* `P_k²` and
    numerator literally **contains `P_{k+1}`**.  So the relation is an identity
    (`P_{k+1}` in terms of itself), not a recurrence — there is no `q`-rational
    multiplier free of the higher `P`.  Also `P_k² ∤ P_{k−1}P_{k+1}` (`P_N`
    irreducible), and `P_N` is *not* coefficient-log-concave in `N`
    (`P_k²−P_{k−1}P_{k+1}` is sign-mixed), so the natural log-concavity that
    would tame the relation fails.  Dead as a self-contained induction.

# What *is* proved here (axiom-clean; no `Classical`/`sorry`/`native_decide`).

  * `cCol4` — the column-4 closed form `6·c_4(N) = 4N⁴+20N³−97N²+73N−30` as a
    `Nat → Q'` (integer-numerator) function.
  * `cCol4_nonneg` — `0 ≤ cCol4 N` for **every** `N ≥ 4` (a genuine `∀N`
    theorem, via the substitution `N = M+4` giving an all-nonneg-coefficient
    polynomial in `M`, then `omega`).
  * `cCol4_matches` — `6·colCoeff P4 4 = cCol4 4` (`decide`): the closed form
    agrees with the actual `P_4` column-4 coefficient (`c_4(4)=169`).

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`,
no `native_decide`.
-/

import YMGap.Continuum.LGVPositivity

namespace YMGap.Continuum.PNDet

open YMGap.Constructive
open YMGap.Continuum.LGV (colCoeff)

/-! ## The column-4 closed form

`P_N(a) = Σ_j c_j(N) a^{2j}`.  The fifth-lowest column is

    c_4(N) = (4N⁴ + 20N³ − 97N² + 73N − 30) / 6,

a degree-4 polynomial in `N` with leading coefficient `2⁴/4! = 2/3`.  We certify
it through the integer numerator `6·c_4(N)` (so nonnegativity reduces to an `Int`
inequality), as `LGVPositivity` does for `3·c_3`. -/

/-- `6·c_4(N) = 4N⁴ + 20N³ − 97N² + 73N − 30`, as an integer expression in `N`
(powers written as explicit products, the project being mathlib-free).
(`c_4` itself has denominator `6`; we certify nonnegativity through `6·c_4`.) -/
def cCol4 (N : Nat) : Q' :=
  Q'.ofInt (4 * ((N : Int) * (N : Int) * ((N : Int) * (N : Int)))
            + 20 * ((N : Int) * (N : Int) * (N : Int))
            - 97 * ((N : Int) * (N : Int))
            + 73 * (N : Int) - 30)

/-- Abstract linear core (powers named as atoms `p2,p3,p4`).  Once the product
identities and the distributed expansion `hexp` are supplied, the
nonnegativity is linear in the atoms and `omega` closes it (using `p2 ≥ 16`
from `x ≥ 4`). -/
private theorem quartic_abs (x p2 p3 p4 : Int)
    (_h2 : p2 = x * x) (_h3 : p3 = p2 * x) (_h4 : p4 = p2 * p2)
    (hx : 4 ≤ x)
    (hexp : p2 * (4 * p2 + 20 * x - 97) = 4 * p4 + 20 * p3 - 97 * p2) :
    0 ≤ 4 * p4 + 20 * p3 - 97 * p2 + 73 * x - 30 := by
  have hp2 : 16 ≤ p2 := by
    have := Int.mul_le_mul hx hx (by omega) (by omega); omega
  have hinner : 0 ≤ 4 * p2 + 20 * x - 97 := by omega
  have hprod : 0 ≤ p2 * (4 * p2 + 20 * x - 97) := Int.mul_nonneg (by omega) hinner
  rw [hexp] at hprod; omega

/-! ## Uniform-in-`N` nonnegativity of column 4

`6·c_4(N) ≥ 0` for every `N ≥ 4`.  Writing `N = M + 4` (`M ≥ 0`) turns the
quartic into a polynomial with **all-nonnegative** coefficients,

    6·c_4(M+4) = 4M⁴ + 84M³ + 527M² + 1281M + 1014,

which is manifestly `≥ 0`; `omega` discharges the cast arithmetic. -/

/-- **`6·c_4(N) ≥ 0` for `N ≥ 4`** (`= 4N⁴+20N³−97N²+73N−30`); uniform in `N`.
Grouping `4N⁴+20N³−97N² = N²·(4N²+20N−97)`, and for `N ≥ 4` the inner factor
`4N²+20N−97 ≥ 4·16+20·4−97 = 47 ≥ 0` and `N² ≥ 16 ≥ 0`, so the product is `≥ 0`;
the linear tail `73N−30 ≥ 0` is added by `omega`.  No `ring`/`nlinarith` — pure
`Int` products + `omega`. -/
theorem cCol4_nonneg {N : Nat} (hN : 4 ≤ N) : (0 : Q') ≤ cCol4 N := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ 4 * ((N : Int) * (N : Int) * ((N : Int) * (N : Int)))
            + 20 * ((N : Int) * (N : Int) * (N : Int))
            - 97 * ((N : Int) * (N : Int)) + 73 * (N : Int) - 30
  have hN4 : (4 : Int) ≤ (N : Int) := by exact_mod_cast hN
  -- The distributed expansion `(x*x)·(4(x*x)+20x−97)`, by core `Int` ring lemmas.
  have hexp : ((N : Int) * (N : Int)) * (4 * ((N : Int) * (N : Int)) + 20 * (N : Int) - 97)
      = 4 * (((N : Int) * (N : Int)) * ((N : Int) * (N : Int)))
        + 20 * (((N : Int) * (N : Int)) * (N : Int)) - 97 * ((N : Int) * (N : Int)) := by
    rw [Int.mul_sub, Int.mul_add]
    rw [show ((N : Int) * (N : Int)) * (4 * ((N : Int) * (N : Int)))
          = 4 * (((N : Int) * (N : Int)) * ((N : Int) * (N : Int))) by
          rw [← Int.mul_assoc, Int.mul_comm ((N : Int) * (N : Int)) 4, Int.mul_assoc]]
    rw [show ((N : Int) * (N : Int)) * (20 * (N : Int))
          = 20 * (((N : Int) * (N : Int)) * (N : Int)) by
          rw [← Int.mul_assoc, Int.mul_comm ((N : Int) * (N : Int)) 20, Int.mul_assoc]]
    rw [Int.mul_comm ((N : Int) * (N : Int)) 97]
  have h := quartic_abs (N : Int) ((N : Int) * (N : Int))
    (((N : Int) * (N : Int)) * (N : Int)) (((N : Int) * (N : Int)) * ((N : Int) * (N : Int)))
    rfl rfl rfl hN4 hexp
  omega

/-! ## Agreement with the actual `P_N` coefficient

The column-4 coefficient sits at index `2·4 = 8` of the residual coefficient
list.  `Favard.P4` carries the genuine `P_4`; its `a⁸` coefficient is
`c_4(4) = 169 = (4·256+20·64−97·16+73·4−30)/6`. -/

/-- `6·c_4(4) = cCol4 4` matches the actual `P_4` column-4 coefficient
(`c_4(4)=169`, so `6·169 = 1014`).  `decide` on `Q'`. -/
theorem cCol4_matches : Q'.ofInt 6 * colCoeff P4 4 = cCol4 4 := by decide

/-- `6·c_4(5) = cCol4 5` matches the actual `P_5` column-4 coefficient
(`c_4(5)=485`); `LGV.P5` is the order-5 residual.  `decide`. -/
theorem cCol4_matches_P5 : Q'.ofInt 6 * colCoeff LGV.P5 4 = cCol4 5 := by decide

end YMGap.Continuum.PNDet

/-! ## OPEN obligation — sharp Wall-1 statement

**Proved here (axiom-clean), the new content:**

  * `cCol4` / `cCol4_nonneg` — the column-4 closed form
    `6·c_4(N) = 4N⁴+20N³−97N²+73N−30`, proved nonnegative for **every** `N ≥ 4`
    (a genuine `∀N` theorem over `Q'`), extending the uniform bottom-strip
    nonnegativity of `LGVPositivity` (`c_0,…,c_3`) by one column.
  * `cCol4_matches` / `cCol4_matches_P5` — agreement of the closed form with the
    actual `P_4`, `P_5` column-4 coefficients (`c_4(4)=169`, `c_4(5)=485`),
    `decide`-certified.

**Ruled out as self-contained closers (exact computer algebra; see header):**

  * a positive symplectic-character / principal-Schur combination for `P_N`
    (exact Farkas infeasibility already at `N=2`);
  * naive LGV / coefficient-total-nonnegativity of the Gram (sign-mixed `2×2`
    minors of `a·G`; the staircase `h_n` is not a positive moment sequence);
  * a Dodgson–Toda induction off `β_k=(q^k−1)²·P_{k+1}P_{k−1}/P_k²` (circular —
    numerator contains `P_{k+1}`; `P_k²∤P_{k−1}P_{k+1}`; not log-concave in `N`).

**OPEN — the single sharpest remaining gap:** a **uniform (N-indexed)** proof of
`nonnegCoeffs P_N` for all `N`.  Equivalently (`PNInduction`): the uniform
first-difference positivity `UniformPNDiffNonneg`, i.e. `P_{N+1} − P_N` is
coefficient-nonneg for all `N` (verified `N ≤ 9` by exact computer algebra; an
`N`-indexed proof is open).  The column-polynomial fragment proved here is
genuinely uniform but covers only the lowest `O(1)` of the `Θ(N³)` columns of
each `P_N`; the bulk (coefficients at `k ∼ N³`) sits in the boundary region the
column-in-`N` description cannot reach.  The lone surviving research route is a
**non-principal vicious-walker / LGV path sum** realizing `p_N(q)` with a
charge/major-index statistic that resolves the genuine determinantal
cancellation of the nonneg-coefficient matrix `a·G`; it was not constructed.
-/

#print axioms YMGap.Continuum.PNDet.cCol4_nonneg
#print axioms YMGap.Continuum.PNDet.cCol4_matches
#print axioms YMGap.Continuum.PNDet.cCol4_matches_P5
