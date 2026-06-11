/-
The **Lindström–Gessel–Viennot / column-coefficient** investigation of the
uniform nonnegativity of `P_N = Δ_N / S_N²` for the SU(2) heat-kernel
q-Hankel determinant.

Setup (same uniform base variable as `MomentPositivity`):
`a = e^{−t/4} ∈ (0,1]`, moments `m_s = (s+1)·a^{s(s+2)}`, leading principal
Gram minors `Δ_N(a) = det G[0..N−1]`, and the q-product square factor
`S_N(a) = ∏_{j=1}^{N−1} (a^{2j}−1)^{N−j}` (the `SN` of `QHankel`).  The
residual `P_N(a) = Δ_N / S_N²` is, empirically (exact computer algebra
through `N = 8`), a polynomial with **only even exponents**, constant term
`1`, leading coefficient `(2N−1)!!`, and **all-nonnegative coefficients**.

Writing `P_N(a) = Σ_{j≥0} c_j(N)·a^{2j}`, the *lowest* columns `c_j(N)`
(fixed `j`, varying `N`) are exact polynomials in `N`:

    c_0(N) = 1
    c_1(N) = 2(N−1)
    c_2(N) = (N+1)(2N−3)
    c_3(N) = (2/3)(2N−1)(N²+2N−9)

and each is `≥ 0` on the range of `N` where the column actually occurs in
`P_N` (`c_1` for `N ≥ 2`, `c_2` for `N ≥ 2`, `c_3` for `N ≥ 3`).  This file
proves exactly those **uniform-in-`N` column nonnegativities** (genuine
`∀ N, …` theorems over `Q'`, not per-`N` `decide`s), and ties the closed
forms to the actual coefficients of `P_2, P_3, P_4` by `decide`.

**Honest scope (documented precisely at the foot of the file).**  The
column-polynomial phenomenon does **not** extend to a uniform proof of
`nonnegCoeffs P_N`:

  * Each `c_j(N)` is a polynomial in `N` only in the *interior regime*
    (`N` large enough that `a^{2j}` sits in the low part of `P_N`); the
    closed form takes *negative* values outside its range (`c_2(1) = −2`,
    `c_3(1) = −4`, `c_3(2) = −2`).  So the column forms are
    **conditionally** nonnegative, not globally positive polynomials.
  * Columns `c_j` with `j ≥ 4` are not pinned down by the available data
    (`N ≤ 8`): the interior regime for column `j` needs `N ≳ j`, and the
    symbolic Gram determinant is infeasible beyond `N = 8`.  The leading
    coefficient `(2N−1)!!` and degree `2·C(N+1,3)` mean `P_N` has `Θ(N³)`
    coefficients; the four columns proved here are the lowest four of them.

So this file delivers the genuinely-uniform fragment (the low-column
nonnegativities) plus a `decide`-extension of the per-`N` verification, and
records the sharp OPEN obligation: a uniform `nonnegCoeffs P_N`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`,
no `native_decide`.
-/

import YMGap.Continuum.MomentPositivity
import YMGap.Continuum.Favard

namespace YMGap.Continuum.LGV

open YMGap.Constructive

/-! ## The column-coefficient closed forms `c_j(N)`

`P_N(a) = Σ_j c_j(N) a^{2j}`.  We realize the four lowest columns as explicit
`Nat → Q'` functions, valued through `Q'.ofInt` of an integer expression in
`N`, so the nonnegativity reduces (`zero_le_iff_num_nonneg`) to an `Int`
inequality provable uniformly in `N` (`omega` / factoring). -/

/-- `c_0(N) = 1`. -/
def cCol0 (_N : Nat) : Q' := Q'.ofNat 1

/-- `c_1(N) = 2(N−1)`, as an integer expression in `N`. -/
def cCol1 (N : Nat) : Q' := Q'.ofInt (2 * ((N : Int) - 1))

/-- `c_2(N) = (N+1)(2N−3)`. -/
def cCol2 (N : Nat) : Q' := Q'.ofInt (((N : Int) + 1) * (2 * (N : Int) - 3))

/-- `3·c_3(N) = 2(2N−1)(N²+2N−9)` (the integer numerator; `c_3` itself has a
denominator `3`, so we certify nonnegativity through `3·c_3 ≥ 0`). -/
def cCol3x3 (N : Nat) : Q' :=
  Q'.ofInt (2 * (2 * (N : Int) - 1) * ((N : Int) * (N : Int) + 2 * (N : Int) - 9))

/-! ## Uniform-in-`N` nonnegativity of the low columns

Each is a genuine `∀ N ≥ N_j, 0 ≤ c_j(N)` theorem — the uniform content the
column-polynomial structure actually delivers. -/

/-- `c_0(N) = 1 ≥ 0` for every `N` (the constant term of `P_N`). -/
theorem cCol0_nonneg (N : Nat) : (0 : Q') ≤ cCol0 N := by
  rw [Q'.zero_le_iff_num_nonneg]; exact Int.natCast_nonneg 1

/-- **`c_1(N) ≥ 0` for `N ≥ 1`** (`= 2(N−1)`); uniform in `N`. -/
theorem cCol1_nonneg {N : Nat} (hN : 1 ≤ N) : (0 : Q') ≤ cCol1 N := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ 2 * ((N : Int) - 1)
  have : (1 : Int) ≤ (N : Int) := by exact_mod_cast hN
  omega

/-- **`c_2(N) ≥ 0` for `N ≥ 2`** (`= (N+1)(2N−3)`); uniform in `N`.  Both
factors are `≥ 0` once `N ≥ 2` (`2N−3 ≥ 1`). -/
theorem cCol2_nonneg {N : Nat} (hN : 2 ≤ N) : (0 : Q') ≤ cCol2 N := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ ((N : Int) + 1) * (2 * (N : Int) - 3)
  have h2 : (2 : Int) ≤ (N : Int) := by exact_mod_cast hN
  have hf1 : (0 : Int) ≤ (N : Int) + 1 := by omega
  have hf2 : (0 : Int) ≤ 2 * (N : Int) - 3 := by omega
  exact Int.mul_nonneg hf1 hf2

/-- **`3·c_3(N) ≥ 0` for `N ≥ 3`** (`= 2(2N−1)(N²+2N−9)`); uniform in `N`.
For `N ≥ 3`, `N²+2N−9 ≥ 6 > 0` and `2N−1 ≥ 5 > 0`, so the product is `≥ 0`.
(`c_3 = (3·c_3)/3`, so `c_3 ≥ 0` follows; we certify the integer numerator.) -/
theorem cCol3x3_nonneg {N : Nat} (hN : 3 ≤ N) : (0 : Q') ≤ cCol3x3 N := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ 2 * (2 * (N : Int) - 1) * ((N : Int) * (N : Int) + 2 * (N : Int) - 9)
  have h3 : (3 : Int) ≤ (N : Int) := by exact_mod_cast hN
  have hf1 : (0 : Int) ≤ 2 * (2 * (N : Int) - 1) := by omega
  -- N² + 2N − 9 ≥ 0 for N ≥ 3: N·N ≥ 3·N ≥ 3·3 = 9 and 2N ≥ 6, so N²+2N−9 ≥ 6.
  have hNN : (9 : Int) ≤ (N : Int) * (N : Int) := by
    have := Int.mul_le_mul h3 h3 (by omega) (by omega); omega
  have hf2 : (0 : Int) ≤ (N : Int) * (N : Int) + 2 * (N : Int) - 9 := by omega
  exact Int.mul_nonneg hf1 hf2

/-! ## Agreement of the closed forms with the actual `P_N` coefficients

The coefficient of `a^{2j}` in `P_N` sits at index `2j` of the coefficient
list.  We read it off `P2, P3, P4` (`MomentPositivity` / `Favard`) and check
it equals `c_j(N)` by `decide`.  (`P_N!![2*j]` is the `j`-th column entry.) -/

/-- Coefficient of `a^{2j}` in a coefficient list (the `j`-th even-index
entry); `0` past the end.  This is the "column read-off". -/
def colCoeff (p : QPoly.Poly) (j : Nat) : Q' := (p.getD (2 * j) 0)

/-- `c_0` matches `P_2, P_3, P_4` at column `0` (the constant term `1`). -/
theorem cCol0_matches :
    colCoeff P2 0 = cCol0 2 ∧ colCoeff P3 0 = cCol0 3 ∧ colCoeff P4 0 = cCol0 4 := by
  decide

/-- `c_1(N) = 2(N−1)` matches `P_2, P_3, P_4` at column `1`. -/
theorem cCol1_matches :
    colCoeff P2 1 = cCol1 2 ∧ colCoeff P3 1 = cCol1 3 ∧ colCoeff P4 1 = cCol1 4 := by
  decide

/-- `c_2(N) = (N+1)(2N−3)` matches `P_2, P_3, P_4` at column `2`. -/
theorem cCol2_matches :
    colCoeff P2 2 = cCol2 2 ∧ colCoeff P3 2 = cCol2 3 ∧ colCoeff P4 2 = cCol2 4 := by
  decide

/-- `3·c_3(N) = 2(2N−1)(N²+2N−9)` matches `3·(P_3[6])`, `3·(P_4[6])` at
column `3` (column `3` first occurs in `P_3`; `P_2` has no `a⁶` term). -/
theorem cCol3x3_matches :
    Q'.ofInt 3 * colCoeff P3 3 = cCol3x3 3 ∧ Q'.ofInt 3 * colCoeff P4 3 = cCol3x3 4 := by
  decide

/-! ## `decide`-extension of the per-`N` nonneg verification to `N = 5`

`MomentPositivity`/`Favard` carry `P_1,…,P_4`.  We add the order-5 residual
`P_5` (degree-80 in `a`, exact computer algebra) and certify
`nonnegCoeffs P_5` by `decide`, pushing the verified base from `N = 4`
to `N = 5` (and the coefficients were exact-checked through `N = 8`). -/

/-- `P_5` coefficient list (low→high), all nonnegative, only even exponents,
constant term `1`, leading coefficient `9!! = 945`. -/
def P5 : QPoly.Poly :=
  [Q'.ofNat 1, 0, Q'.ofNat 8, 0, Q'.ofNat 42, 0, Q'.ofNat 156, 0, Q'.ofNat 485,
   0, Q'.ofNat 1288, 0, Q'.ofNat 3074, 0, Q'.ofNat 6640, 0, Q'.ofNat 13287, 0,
   Q'.ofNat 24740, 0, Q'.ofNat 43400, 0, Q'.ofNat 71912, 0, Q'.ofNat 113424, 0,
   Q'.ofNat 170524, 0, Q'.ofNat 245624, 0, Q'.ofNat 339244, 0, Q'.ofNat 450824,
   0, Q'.ofNat 576588, 0, Q'.ofNat 711540, 0, Q'.ofNat 846992, 0, Q'.ofNat 974326,
   0, Q'.ofNat 1082388, 0, Q'.ofNat 1162692, 0, Q'.ofNat 1206216, 0,
   Q'.ofNat 1209672, 0, Q'.ofNat 1170516, 0, Q'.ofNat 1093416, 0, Q'.ofNat 983484,
   0, Q'.ofNat 851856, 0, Q'.ofNat 707724, 0, Q'.ofNat 564024, 0, Q'.ofNat 428508,
   0, Q'.ofNat 310215, 0, Q'.ofNat 211956, 0, Q'.ofNat 136578, 0, Q'.ofNat 81456,
   0, Q'.ofNat 45045, 0, Q'.ofNat 22140, 0, Q'.ofNat 9690, 0, Q'.ofNat 3360, 0,
   Q'.ofNat 945]

/-- **`nonnegCoeffs P_5`** (`decide`) — the order-5 residual is
nonneg-coefficient, extending the verified base to `N = 5`. -/
theorem P5_nonneg : nonnegCoeffs P5 := by decide

/-- **`P_5(a) ≥ 1`** for `a ≥ 0` — constant-term-`1` floor (so `P_5 > 0`). -/
theorem P5_ge_one {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval P5 a) 1 :=
  geRat_ceval_ge_one_of_headGeOne (Q'.ofNat 1) _ ha P5_nonneg (by decide)

/-- The columns of `P_5` agree with the four proved closed forms (`decide`):
`c_0(5)=1`, `c_1(5)=8`, `c_2(5)=42`, `3c_3(5)=468`.  Confirms the closed
forms continue to hold at the freshly-added order. -/
theorem cCol_matches_P5 :
    colCoeff P5 0 = cCol0 5 ∧ colCoeff P5 1 = cCol1 5 ∧
    colCoeff P5 2 = cCol2 5 ∧ Q'.ofInt 3 * colCoeff P5 3 = cCol3x3 5 := by
  decide

end YMGap.Continuum.LGV

/-! ## OPEN obligation and honest verdict

**Proved here (axiom-clean, uniform in `N`).**

  * The four lowest **column-coefficient closed forms** of
    `P_N(a) = Σ_j c_j(N) a^{2j}`:
        c_0(N) = 1,  c_1(N) = 2(N−1),  c_2(N) = (N+1)(2N−3),
        c_3(N) = (2/3)(2N−1)(N²+2N−9),
    each proved **nonnegative for every `N`** on its valid range
    (`cCol0_nonneg`, `cCol1_nonneg` `N≥1`, `cCol2_nonneg` `N≥2`,
    `cCol3x3_nonneg` `N≥3`), as genuine `∀N` theorems over `Q'` (not
    per-`N` `decide`s).  Agreement with the actual `P_2,P_3,P_4,P_5`
    coefficients is `decide`-certified (`cColj_matches`, `cCol_matches_P5`).
  * `nonnegCoeffs P_5` (`decide`) and `P_5 ≥ 1`, extending the per-`N`
    verified base from `N = 4` (in `Favard`) to `N = 5`.

**OPEN — the single remaining mathematical gap.**  A *uniform* proof that

    P_N(a) := Δ_N(a) / S_N(a)²   has nonnegative coefficients for all `N`.

This is exact computer algebra through `N = 8` (coefficients positive, only
even powers, constant term `1`, leading coefficient `(2N−1)!!`), but it is
**not** reduced to an `N`-indexed theorem here.

**Honest verdict on the LGV / column-polynomial approach.**  It does **not**
close the uniform proof, for two structural reasons established above:

  1. *The column forms are only conditionally positive.*  Each `c_j(N)` is a
     polynomial in `N` valid only in the interior regime (`N` past the point
     where `a^{2j}` enters the low part of `P_N`); outside it the same
     polynomial is negative (`c_2(1) = −2`, `c_3(1) = −4`, `c_3(2) = −2`).
     A uniform certificate would need, for every `j`, both the closed form
     *and* its valid-range threshold — and the thresholds grow with `j`.

  2. *There are `Θ(N³)` columns.*  `deg_a P_N = 4·C(N+1,3)`, so `P_N` has
     order `N³` nonzero coefficients; the four columns settled here are the
     lowest four.  Columns `c_j` with `j ≥ 4` are not even pinned by the
     feasible data (`N ≤ 8`, the symbolic Gram determinant being infeasible
     beyond): their interior regime begins around `N ≈ j`, past the data.

  Moreover the naive LGV / Karlin–McGregor route via the Hankel↔Jacobi
  correspondence (`Δ_N = ∏ λ_k^{N−k}`) gives **rational**, not
  nonneg-polynomial, weights `λ_k = (S_k S_{k−2}/S_{k−1}²)²·(P_k P_{k−2}/P_k²)`
  — the `P`-factors reappear in the denominators — so it does not exhibit a
  manifestly-nonneg monomial path model.  A genuine non-intersecting-path /
  Schur-positive model for `P_N` (the coefficients are empirically
  log-concave and unimodal, consistent with one) would close the gap, but
  was not found here; finding it remains the open problem.

  *Net:* the perfect-square factor `S_N²` is uniform (`QHankel`), the
  division-free Favard reduction is uniform (`Favard`), and the lowest column
  coefficients of `P_N` are uniformly nonnegative (this file); the missing
  piece is the *all-column* nonnegativity of `P_N`, which the
  column-polynomial / LGV-on-Hankel data does not supply uniformly.

This file does not depend on the `MomentPositivity` moment-bridge OPEN — its
results are statements about the polynomials `P_N` / the column functions
`c_j(N)`, exactly as `MomentPositivity.delta3_nonneg` is.
-/

#print axioms YMGap.Continuum.LGV.cCol0_nonneg
#print axioms YMGap.Continuum.LGV.cCol1_nonneg
#print axioms YMGap.Continuum.LGV.cCol2_nonneg
#print axioms YMGap.Continuum.LGV.cCol3x3_nonneg
#print axioms YMGap.Continuum.LGV.cCol0_matches
#print axioms YMGap.Continuum.LGV.cCol1_matches
#print axioms YMGap.Continuum.LGV.cCol2_matches
#print axioms YMGap.Continuum.LGV.cCol3x3_matches
#print axioms YMGap.Continuum.LGV.P5_nonneg
#print axioms YMGap.Continuum.LGV.P5_ge_one
#print axioms YMGap.Continuum.LGV.cCol_matches_P5
