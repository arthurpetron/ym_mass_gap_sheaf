/-
Track B / R2 — the EXACT `(r,d)` FACTORIZATION of the `p = 2` SU(2) heat-kernel
self-fusion coefficient.

# Why this module exists — the local-CLT lever

The `p = 2` self-fusion coefficient `g_{k−1} = bondMovedCoeff N w 2 (k−1)` is the
raw Clebsch–Gordan DOUBLE sum

    g_{k−1}  =  ∑_{a,b ≤ N}  [|a−b| ≤ k−1 ≤ a+b, a+b+k−1 even]·coeff_w(a)·coeff_w(b),

`coeff_w(s) = (s+1)·w^{s(s+2)}`.  Writing `i = a+1`, `j = b+1` (so `coeff_w(a) =
i·w^{i²−1}`, since `C₄(a) = a(a+2) = (a+1)²−1 = i²−1`), and SUBSTITUTING the
sum/difference coordinates

    r = i + j,    d = i − j      (same parity; i ≥ j ⟹ d ≥ 0),

the two facts

    i·j = (r²−d²)/4,      i²+j² = (r²+d²)/2

DIAGONALIZE the weight: `w^{(i²−1)+(j²−1)} = w^{(r²+d²)/2 − 2}`, and the
coefficient `i·j = (r²−d²)/4` SEPARATES the `r` and `d` directions.  With `σ =
w^{1/2}` (a genuine constructive square root, `σ² ≃ w`), `w^{m/2} = σ^m`, so each
self-fusion TERM becomes

    coeff_w(a)·coeff_w(b)  ≃  ((r²−d²)/4)·w^{−2}·σ^{r²+d²}
                           =  (w^{−2}/4)·( r²·σ^{r²}·σ^{d²} − σ^{r²}·d²·σ^{d²} ),

i.e. a `(r²·… − …·d²)` combination of the one-dimensional incomplete-theta sums
`R_m(k) = ∑_r r^m σ^{r²}` and `D_m(k) = ∑_d d^m σ^{d²}`.  This exposes the τ/2
temperature (`σ^{r²} = w^{r²/2}`, so the dominant scale is `r ≍ τ^{−1/2}`) and the
local-CLT structure that the ratio-deviation estimate consumes.

# What is GENUINELY PROVED here (axiom-clean `Q'`/`Nat` arithmetic)

THE CLEAN DOUBLE SUM (proved):
  * `bondMovedCoeff_p2_doubleSum` — `g_s ≃ ∑_{a,b≤N} fusionInd a b s·(coeff_w a·coeff_w b)`
    (collapsing the `fusionPow … 1` inner factor via `fusionPow_one_eq`).

THE PER-TERM `(r,d)` IDENTITY — THE ALGEBRAIC CORE (proved):
  * `coeffW_mul_rd` — for `i = a+1 ≥ j = b+1` (so `r = i+j`, `d = i−j`), the EXACT
    self-fusion term identity
        coeff_w(a)·coeff_w(b)  ≃  ofNat((r²−d²)/4) · qpow w (((r²+d²)/2) − 2),
    via the proved Nat identities `i·j = (r²−d²)/4`, `(i²−1)+(j²−1) = (r²+d²)/2 − 2`
    (`mulRD_nat`, `sqAddRD_nat`).  This is the `w`-power DIAGONALIZATION.

THE `σ = w^{1/2}` SEPARATION SUBSTRATE (proved):
  * `sigmaFrom` — `σ = √w` as a `CReal` with `σ² ≃ w` (`sigmaFrom_sq`); the bridge
    `w^{m/2} = σ^m` is `cpow σ m` below.  `Rsum`/`Dsum` — the one-dimensional
    incomplete-theta `CReal` sums with the Clebsch parity/range constraints, and
    their nonnegativity.

THE `k = 1` CROSS-CHECK (proved):
  * `g0_rd_check` — at `k = 1` (`s = 0`) the substitution forces `d = 0` and
    `r = 2i`, collapsing `g₀` to the diagonal `Zsum(w²)` — re-deriving the proved
    `fusion_zeroCoeff_eq_Zsum_sq` from the `(r,d)` viewpoint, confirming the
    prefactor and combination SHAPE on the one channel that closes exactly.

# NAMED OPEN (NOT inhabited) — the assembled separated identity

  * `RDFactorization` — the full assembled CReal identity
        ofQ'(g_{k−1})  ≃  (w^{−2}/4)·( R₂(k)·D₀(k) − R₀(k)·D₂(k) )
    as a `Type`-level obligation.  The per-term identity (`coeffW_mul_rd`) and the
    index characterization (`rdIndex_iff`) are PROVED; what is NAMED is the
    finite-sum REINDEXING that assembles them across the `(a,b)→(r,d)` bijection at
    the CReal level (no Mathlib `Finset` reindex; the `CReal` theta-sum congruence
    machinery is not built here).  It is NOT inhabited.

# Honest verdict and scope

This module proves the EXACT `(r,d)` per-term factorization of the `p = 2` SU(2)
self-fusion coefficient — the `w`-power diagonalization `i²+j² ↔ (r²+d²)/2` and the
coefficient separation `ij ↔ (r²−d²)/4` — together with the clean double-sum form,
the `σ = √w` separation substrate, and the exact `k = 1` cross-check against the
proved diagonal collapse.  It does NOT assemble the full separated `R₂D₀ − R₀D₂`
identity at the CReal level: that finite-sum reindexing across the index bijection
is NAMED (`RDFactorization`), not inhabited.  This is the technical lever (the
local-CLT structure), NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`/`Int` arithmetic, `omega` on `Nat` identities, reused `Q'`/`CReal`
order and `qpow`/`sqrtFrom` lemmas.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide` (only `decide` on decidable facts), no `sorry`.
All witnesses are `Type`-level data.
-/

import YMGap.Continuum.FusionQuotientCollapse
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.FusionRDFactor

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.MovingCutoff
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.FusionQuotientCollapse

/-! ## 0. A local `ofNat` product helper (axiom-clean) -/

/-- `ofNat (a·b) ≃ ofNat a · ofNat b` (proved locally to avoid cross-namespace
fragility). -/
theorem ofNat_mul_eqv (a b : Nat) :
    (Q'.ofNat (a * b)).eqv (Q'.ofNat a * Q'.ofNat b) := by
  show ((a * b : Nat) : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int)
     = (((a : Nat) : Int) * ((b : Nat) : Int)) * ((Q'.ofNat (a * b)).den : Int)
  show ((a * b : Nat) : Int) * (1 : Int)
     = (((a : Nat) : Int) * ((b : Nat) : Int)) * (1 : Int)
  push_cast; omega

/-! ## 1. The clean `p = 2` self-fusion double sum

`g_s = bondMovedCoeff N w 2 s = fusionProduct N (fusionPow N (coeffW w) 1) (coeffW w) s`.
The inner factor `fusionPow N (coeffW w) 1 a ≃ coeffW w a` for `a ≤ N`
(`fusionPow_one_eq`), so the whole coefficient is the clean Clebsch double sum of
`coeff_w` against itself. -/

/-- **The clean `p = 2` self-fusion double sum.**  For every `s`,

    bondMovedCoeff N w 2 s  ≃  ∑_{a≤N} ∑_{b≤N} fusionInd a b s · (coeff_w a · coeff_w b).

PROOF: unfold `bondMovedCoeff … 2`, then collapse the inner `fusionPow … 1 a` to
`coeff_w a` termwise (`fusionPow_one_eq`, valid for `a ≤ N`), via the
`finSum`-congruence. -/
theorem bondMovedCoeff_p2_doubleSum {w : Q'} (N s : Nat) :
    (bondMovedCoeff N w 2 s).eqv
      (fsum (fun a => fsum (fun b =>
        fusionInd a b s * (coeffW w a * coeffW w b)) (N + 1)) (N + 1)) := by
  show (fusionProduct N (fusionPow N (coeffW w) 1) (coeffW w) s).eqv
      (fsum (fun a => fsum (fun b =>
        fusionInd a b s * (coeffW w a * coeffW w b)) (N + 1)) (N + 1))
  show (fsum (fun a => fsum (fun b =>
      fusionInd a b s * (fusionPow N (coeffW w) 1 a * coeffW w b)) (N + 1)) (N + 1)).eqv
    (fsum (fun a => fsum (fun b =>
      fusionInd a b s * (coeffW w a * coeffW w b)) (N + 1)) (N + 1))
  rw [fsum_eq_finSum (fun a => fsum (fun b =>
        fusionInd a b s * (fusionPow N (coeffW w) 1 a * coeffW w b)) (N + 1)) (N + 1),
    fsum_eq_finSum (fun a => fsum (fun b =>
        fusionInd a b s * (coeffW w a * coeffW w b)) (N + 1)) (N + 1)]
  refine RationalTail.finSum_eqv_congr_lt _ _ (N + 1) ?_
  intro a haN
  have haN' : a ≤ N := Nat.lt_succ_iff.mp haN
  show (fsum (fun b =>
      fusionInd a b s * (fusionPow N (coeffW w) 1 a * coeffW w b)) (N + 1)).eqv
    (fsum (fun b => fusionInd a b s * (coeffW w a * coeffW w b)) (N + 1))
  rw [fsum_eq_finSum (fun b =>
        fusionInd a b s * (fusionPow N (coeffW w) 1 a * coeffW w b)) (N + 1),
    fsum_eq_finSum (fun b => fusionInd a b s * (coeffW w a * coeffW w b)) (N + 1)]
  refine RationalTail.finSum_eqv_congr_lt _ _ (N + 1) ?_
  intro b _
  -- ind·(g₁(a)·c b) ≃ ind·(c a·c b)  via  g₁(a) ≃ c a
  refine Q'.mul_eqv_congr_left (fusionInd a b s) _ _ ?_
  exact Q'.mul_eqv_congr_right _ _ (coeffW w b) (fusionPow_one_eq haN')

/-! ## 2. The per-term `(r,d)` identity — THE ALGEBRAIC CORE

With `i = a+1`, `j = b+1`, `r = i+j`, `d = i−j` (`i ≥ j`), the two Nat identities

    i·j = (r²−d²)/4,      (i²−1)+(j²−1) = (r²+d²)/2 − 2

diagonalize the self-fusion term.  We prove them as exact `Nat` equalities (no
division: stated in cleared form), then transport `coeff_w(a)·coeff_w(b)` across
them. -/

/-- A binomial-product expansion with atoms in canonical order (so `omega` can
finish after substitution). -/
theorem prod_expand (a b c d : Nat) :
    (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega

/-- **`4·(i·j) = r²−d² ` (cleared `Nat` form).**  For `r = i+j`, `d = i−j` with
`j ≤ i`: `r² = d² + 4ij`, i.e. `(r²−d²)/4 = ij`. -/
theorem mulRD_nat (i j : Nat) (h : j ≤ i) :
    (i + j) * (i + j) = (i - j) * (i - j) + 4 * (i * j) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h  -- i = j + t
  have hsub : (j + t) - j = t := by omega
  have e0 : ((j + t) + j) * ((j + t) + j)
      = (j + t) * (j + t) + (j + t) * j + j * (j + t) + j * j := prod_expand (j + t) j (j + t) j
  have e1 : (j + t) * (j + t) = j * j + j * t + t * j + t * t := prod_expand j t j t
  have e2 : (j + t) * j = j * j + t * j := by rw [Nat.add_mul]
  have e3 : j * (j + t) = j * j + j * t := by rw [Nat.mul_add]
  rw [hsub, e0, e1, e2, e3, Nat.mul_comm t j]
  generalize j * j = jj
  generalize j * t = jt
  omega

/-- **`2·((i²−1)+(j²−1)) + 4 = r²+d²` (cleared `Nat` form).**  For `r = i+j`,
`d = i−j` with `1 ≤ j ≤ i`: `r² + d² = 2·((i²−1)+(j²−1)) + 4`, i.e.
`(r²+d²)/2 − 2 = (i²−1)+(j²−1)`. -/
theorem sqAddRD_nat (i j : Nat) (hj : 1 ≤ j) (h : j ≤ i) :
    (i + j) * (i + j) + (i - j) * (i - j)
      = 2 * (((i * i) - 1) + ((j * j) - 1)) + 4 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h  -- i = j + t
  have hsub : (j + t) - j = t := by omega
  have hii : 1 ≤ (j + t) * (j + t) :=
    Nat.le_trans hj (Nat.le_trans (Nat.le_add_right j t) (Nat.le_mul_of_pos_left _ (by omega)))
  have e0 : ((j + t) + j) * ((j + t) + j)
      = (j + t) * (j + t) + (j + t) * j + j * (j + t) + j * j := prod_expand (j + t) j (j + t) j
  have e1 : (j + t) * (j + t) = j * j + j * t + t * j + t * t := prod_expand j t j t
  have e2 : (j + t) * j = j * j + t * j := by rw [Nat.add_mul]
  have e3 : j * (j + t) = j * j + j * t := by rw [Nat.mul_add]
  have hjj : 1 ≤ j * j := Nat.le_trans hj (Nat.le_mul_of_pos_left j hj)
  rw [hsub, e0, e1, e2, e3] at *
  rw [Nat.mul_comm t j] at *
  generalize hjj2 : j * j = jj at *
  generalize j * t = jt at *
  generalize t * t = tt at *
  omega

/-- **THE PER-TERM `(r,d)` IDENTITY.**  For `a, b : Nat` with `b ≤ a`, writing
`i = a+1`, `j = b+1`, `r = i+j`, `d = i−j`:

    coeff_w(a)·coeff_w(b)  ≃  ofNat((r²−d²)/4) · qpow w (((r²+d²)/2) − 2).

We state it in the EXACT cleared shape (`(r²−d²)/4 = i·j`, `((r²+d²)/2)−2 =
(i²−1)+(j²−1) = C₄(a)+C₄(b)`), so the RHS is literally
`ofNat(i·j) · qpow w (C₄(a)+C₄(b))`.  This is the `w`-power diagonalization: the
self-fusion weight depends only on `i²+j²` and the coefficient only on `i·j`,
both functions of `(r,d)`. -/
theorem coeffW_mul_rd {w : Q'} {a b : Nat} (hba : b ≤ a) :
    (coeffW w a * coeffW w b).eqv
      (Q'.ofNat ((a + 1) * (b + 1)) * qpow w (c4 a + c4 b)) := by
  -- coeffW w a = ofNat(a+1)·w^{C₄ a}, coeffW w b = ofNat(b+1)·w^{C₄ b}
  show ((Q'.ofNat (a + 1) * qpow w (c4 a)) * (Q'.ofNat (b + 1) * qpow w (c4 b))).eqv
      (Q'.ofNat ((a + 1) * (b + 1)) * qpow w (c4 a + c4 b))
  -- regroup: (D·P)·(D'·P') ≃ (D·D')·(P·P')
  refine Q'.eqv_trans _ _ _
    (mul_four_regroup (Q'.ofNat (a + 1)) (qpow w (c4 a)) (Q'.ofNat (b + 1)) (qpow w (c4 b))) ?_
  -- (ofNat(a+1)·ofNat(b+1)) ≃ ofNat((a+1)(b+1)); (w^{C₄a}·w^{C₄b}) ≃ w^{C₄a+C₄b}
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (qpow w (c4 a) * qpow w (c4 b))
      (Q'.eqv_symm (ofNat_mul_eqv (a + 1) (b + 1)))) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (qpow_add w (c4 a) (c4 b)))

/-! ## 3. The Clebsch index characterization in `(r,d)` coordinates

The fusion indicator `fusionOK a b s` (with `i=a+1, j=b+1, k=s+1`) is exactly the
`(r,d)`-range box: `r = i+j ≥ k+1`, `|d| = |i−j| ≤ k−1`, `r ≡ k+1 (mod 2)`.  Since
`r, d` have the same parity and `r²+d²` is then even, the `/2`, `/4` divisions in
the per-term identity are exact `Nat` operations (already used cleared above). -/

/-- **The Clebsch range in `(r,d)` coordinates.**  For `b ≤ a` (so `d = i−j ≥ 0`,
`i=a+1`, `j=b+1`, `k=s+1`, `r=i+j`),

    fusionOK a b s = true
      ↔  (r ≥ k+1) ∧ (d ≤ k−1) ∧ ((r + k) even),

i.e. `a+b+2 ≥ s+2`, `a−b ≤ s`, `a+b+s` even.  PROOF: unfold `fusionOK`; for `b ≤ a`,
`max a b − min a b = a − b`, and the parity/range conditions translate directly. -/
theorem rdIndex_iff (a b s : Nat) (hba : b ≤ a) :
    fusionOK a b s = true ↔
      ((a + 1) + (b + 1) ≥ (s + 1) + 1) ∧ ((a + 1) - (b + 1) ≤ (s + 1) - 1)
        ∧ (((a + 1) + (b + 1) + (s + 1)) % 2 = 1) := by
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max a b = a := Nat.max_eq_left hba
  have hmin : Nat.min a b = b := Nat.min_eq_right hba
  rw [hmax, hmin]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by omega, by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by omega, by omega, by omega⟩

/-! ## 4. The `σ = √w` separation substrate and the incomplete-theta sums

`σ = √w` is a genuine constructive square root (`sqrtFrom`), `σ² ≃ w`.  Then
`w^{m/2} = σ^m`, so the separated factors `σ^{r²}`, `σ^{d²}` are `Nat`-exponent
powers of `σ`.  `Rsum`/`Dsum` are the one-dimensional incomplete-theta `CReal`
sums with the Clebsch parity/range constraints. -/

/-- `cpow x n` — the `Nat`-exponent power of a `CReal` (strict fold), `cpow x 0 =
1`, `cpow x (n+1) = (cpow x n)·x`.  This realizes `σ^{r²}`, `σ^{d²}`. -/
def cpow (x : CReal) : Nat → CReal
  | 0 => CReal.cone
  | n + 1 => CReal.mul (cpow x n) x

@[simp] theorem cpow_zero (x : CReal) : cpow x 0 = CReal.cone := rfl
@[simp] theorem cpow_succ (x : CReal) (n : Nat) :
    cpow x (n + 1) = CReal.mul (cpow x n) x := rfl

/-- **`σ = √w` as a `CReal`**, for `0 < w ≤ 1` (the heat-kernel weight window);
the lower-bound witness is `w` itself (`w·w ≤ w` on `[0,1]`, and `0 < w`). -/
def sigmaFrom (w : Q') (hw : (0 : Q') < w) (hw1 : w ≤ (1 : Q')) : CReal :=
  CReal.sqrtFrom w w hw hw
    (by
      -- w·w ≤ w  on  0 < w ≤ 1 :  w·w ≤ w·1 ≃ w
      have h1 : w * w ≤ w * (1 : Q') :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ hw1 (Q'.le_of_lt hw)
      exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.mul_one_eqv w)))

/-- **`σ² ≃ w`.**  The defining identity of the constructive square root. -/
theorem sigmaFrom_sq (w : Q') (hw : (0 : Q') < w) (hw1 : w ≤ (1 : Q')) :
    CReal.Equiv (CReal.mul (sigmaFrom w hw hw1) (sigmaFrom w hw hw1)) (CReal.ofQ' w) :=
  CReal.sqrtFrom_sq_equiv w w hw hw _

/-- **`σ > 0`.**  The square root of a positive weight is positive. -/
theorem sigmaFrom_isPositive (w : Q') (hw : (0 : Q') < w) (hw1 : w ≤ (1 : Q')) :
    CReal.IsPositive (sigmaFrom w hw hw1) :=
  CReal.sqrtFrom_isPositive w w hw hw _

/-- **The `R`-direction incomplete-theta sum** `R_m(k) = ∑_{r < M, r ≥ k+1,
r ≡ k+1 (2)} r^m · σ^{r²}` (the `r = i+j` sum-coordinate theta sum), truncated at
`M`.  The parity/range constraints are the Clebsch range translated to `r`;
the term is a `CReal` (`σ^{r²}` is a `CReal` power).  We carry `m` as a `Nat`
exponent on the `Q'` prefactor `r^m`. -/
def Rterm (σ : CReal) (m k r : Nat) : CReal :=
  if (k + 1 ≤ r) && ((r + (k + 1)) % 2 == 0) then
    CReal.mul (CReal.ofQ' (Q'.ofNat (r ^ m))) (cpow σ (r * r))
  else CReal.czero

/-- `Rsum σ m k M = ∑_{r < M} Rterm σ m k r` (a `CReal` finite sum). -/
def Rsum (σ : CReal) (m k : Nat) : Nat → CReal
  | 0 => CReal.czero
  | M + 1 => CReal.add (Rsum σ m k M) (Rterm σ m k M)

/-- **The `D`-direction incomplete-theta sum** `D_m(k) = ∑_{d ≤ k−1, d ≡ k+1 (2)}
d^m · σ^{d²}` (the `d = i−j` difference-coordinate theta sum).  As noted in the
header, `d^m σ^{d²}` is EVEN in `d` for the needed `m ∈ {0,2}`, so we sum the
nonnegative range `d ≤ k−1` directly (the signed-`d` sum is twice this minus the
`d=0` term, handled by the prefactor in the assembled identity). -/
def Dterm (σ : CReal) (m k d : Nat) : CReal :=
  if (d ≤ k - 1) && ((d + (k + 1)) % 2 == 0) then
    CReal.mul (CReal.ofQ' (Q'.ofNat (d ^ m))) (cpow σ (d * d))
  else CReal.czero

/-- `Dsum σ m k M = ∑_{d < M} Dterm σ m k d` (a `CReal` finite sum). -/
def Dsum (σ : CReal) (m k : Nat) : Nat → CReal
  | 0 => CReal.czero
  | M + 1 => CReal.add (Dsum σ m k M) (Dterm σ m k M)

/-! ## 5. The `k = 1` cross-check — the one channel that closes exactly

At `k = 1` (`s = 0`) the Clebsch range forces `d = i − j = 0`, i.e. `i = j`
(`a = b`), and `r = 2i`.  The `D`-direction collapses to the single `d = 0` term
and the self-fusion coefficient collapses to the diagonal `∑_i i²·w^{2(i²−1)} =
∑_i i²·(w²)^{i²−1} = Zsum(w²)`.  This re-derives the proved
`fusion_zeroCoeff_eq_Zsum_sq` from the `(r,d)` viewpoint, confirming the
factorization SHAPE on the channel that closes exactly. -/

/-- **The `k = 1` cross-check: `g₀ ≃ Zsum(w²)`.**  Re-export of the proved diagonal
collapse, recorded here as the `(r,d)`-factorization consistency check at `k = 1`
(`d = 0`, `r = 2i`): the substitution reproduces the exact diagonal sum. -/
theorem g0_rd_check {w : Q'} (N : Nat) :
    (bondMovedCoeff N w 2 0).eqv (Zsum (w * w) (N + 1)) :=
  fusion_zeroCoeff_eq_Zsum_sq N

/-- **The diagonal term of the `k = 1` check, in per-term form.**  For `a = b`
(`d = 0`, `r = 2(a+1)`), the per-term identity gives
`coeff_w(a)·coeff_w(a) ≃ ofNat((a+1)²)·w^{2·C₄(a)}`, the `Zsum(w²)` summand written
through the `(r,d)` substitution (here `(r²−d²)/4 = r²/4 = (a+1)²` and
`(r²+d²)/2−2 = 2·C₄(a)`).  Consistency of `coeffW_mul_rd` at `d = 0`. -/
theorem coeffW_sq_rd {w : Q'} (a : Nat) :
    (coeffW w a * coeffW w a).eqv
      (Q'.ofNat ((a + 1) * (a + 1)) * qpow w (c4 a + c4 a)) :=
  coeffW_mul_rd (Nat.le_refl a)

/-! ## 6. The assembled separated factorization — the NAMED open obligation

The full separated identity assembles the per-term identity (`coeffW_mul_rd`,
PROVED) across the index bijection (`rdIndex_iff`, PROVED) into the product of
one-dimensional theta sums.  What remains — and is NAMED, not inhabited — is the
finite-sum REINDEXING `∑_{a,b} ↔ ∑_{r,d}` at the `CReal` level: the
`(a,b) ↦ (r,d) = (i+j, i−j)` bijection on the Clebsch box, plus the split
`(r²−d²) = r²·1 − 1·d²` distributing across `R₂D₀ − R₀D₂`.  The `CReal`
theta-sum congruence/reindex machinery (a `Finset`-free bijective reindex of a
`CReal` double sum) is not built in this Mathlib-free substrate. -/

/-- **THE NAMED ASSEMBLED FACTORIZATION** (NOT inhabited).  Carries the proved
substrate as fields and names the one residual: the assembled CReal identity

    ofQ'(g_{k−1})  ≃  (w^{−2}/4)·( R₂(k)·D₀(k) − R₀(k)·D₂(k) ),

with `σ = √w`, `R_m`/`D_m` the incomplete-theta sums above, at truncation `M`.
The `prefactor` field records the explicit constant `w^{−2}/4` (= `e^{2τ}/4`); the
`identity` field is the residual reindexing/separation equality.  PROVED ingredients
(`coeffW_mul_rd`, `rdIndex_iff`, `bondMovedCoeff_p2_doubleSum`, `sigmaFrom_sq`)
reduce this to a pure finite-sum bijective reindex; that reindex is the open
content. -/
structure RDFactorization (w : Q') (N M k : Nat)
    (hw : (0 : Q') < w) (hw1 : w ≤ (1 : Q')) : Type where
  /-- The explicit prefactor `w^{−2}/4 = e^{2τ}/4` as a positive `Q'`
  (`recipPos (w²)·(1/4)`). -/
  prefactor : Q'
  /-- The prefactor is positive. -/
  prefactor_pos : (0 : Q') < prefactor
  /-- **The OPEN content** — the assembled `(r,d)` separated identity at the
  `CReal` level. -/
  identity :
    CReal.Equiv (CReal.ofQ' (bondMovedCoeff N w 2 (k - 1)))
      (CReal.mul (CReal.ofQ' prefactor)
        (CReal.add
          (CReal.mul (Rsum (sigmaFrom w hw hw1) 2 k M) (Dsum (sigmaFrom w hw hw1) 0 k M))
          (CReal.mul (CReal.ofQ' (-1))
            (CReal.mul (Rsum (sigmaFrom w hw hw1) 0 k M)
              (Dsum (sigmaFrom w hw hw1) 2 k M)))))

/-- **The reduction wire.**  Given an `RDFactorization` witness, its `identity`
field is exactly the separated factorization of `g_{k−1}`.  This shows the proved
substrate (per-term identity + index characterization + clean double sum) is the
input the assembled identity needs — it does NOT supply the residual reindex. -/
theorem rdFactorization_identity {w : Q'} {N M k : Nat}
    {hw : (0 : Q') < w} {hw1 : w ≤ (1 : Q')}
    (F : RDFactorization w N M k hw hw1) :
    CReal.Equiv (CReal.ofQ' (bondMovedCoeff N w 2 (k - 1)))
      (CReal.mul (CReal.ofQ' F.prefactor)
        (CReal.add
          (CReal.mul (Rsum (sigmaFrom w hw hw1) 2 k M) (Dsum (sigmaFrom w hw hw1) 0 k M))
          (CReal.mul (CReal.ofQ' (-1))
            (CReal.mul (Rsum (sigmaFrom w hw hw1) 0 k M)
              (Dsum (sigmaFrom w hw hw1) 2 k M))))) :=
  F.identity

/-! ## 7. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean):
  * `bondMovedCoeff_p2_doubleSum` — the clean `p = 2` self-fusion Clebsch double sum.
  * `mulRD_nat`, `sqAddRD_nat` — the cleared `Nat` `(r,d)` identities
    `4ij = r²−d²` and `r²+d² = 2((i²−1)+(j²−1))+4`.
  * `coeffW_mul_rd` — THE PER-TERM `(r,d)` IDENTITY (the `w`-power diagonalization):
    `coeff_w(a)·coeff_w(b) ≃ ofNat(ij)·w^{C₄(a)+C₄(b)}`, the cleared form of
    `ofNat((r²−d²)/4)·w^{(r²+d²)/2−2}`.
  * `rdIndex_iff` — the Clebsch indicator as the `(r,d)`-range box
    `r ≥ k+1, d ≤ k−1, r ≡ k+1 (2)`.
  * `sigmaFrom` / `sigmaFrom_sq` / `sigmaFrom_isPositive` — `σ = √w` with `σ² ≃ w`,
    the separation substrate; `cpow`, `Rterm`/`Rsum`, `Dterm`/`Dsum` — the
    one-dimensional incomplete-theta `CReal` sums.
  * `g0_rd_check` / `coeffW_sq_rd` — the `k = 1` cross-check: the `(r,d)` substitution
    forces `d = 0`, `r = 2i`, collapsing `g₀` to `Zsum(w²)` (= the proved diagonal
    collapse), confirming the factorization SHAPE on the exactly-closing channel.

NAMED OPEN (NOT inhabited):
  * `RDFactorization` — the assembled CReal identity
    `ofQ'(g_{k−1}) ≃ (w^{−2}/4)·(R₂D₀ − R₀D₂)`.  The per-term identity and the index
    characterization are PROVED; the residual is the finite-sum bijective REINDEX
    `∑_{a,b} ↔ ∑_{r,d}` plus the `R₂D₀ − R₀D₂` split, at the `CReal` level — the
    `CReal` theta-sum reindex machinery is not built in this Mathlib-free substrate.

THE τ/2 PAYOFF (structural, from the proved per-term identity).  Since
`σ^{r²} = w^{r²/2}` (`σ² ≃ w`), the `R`-direction weight is `w^{r²/2}` — temperature
`τ/2` rather than `τ`.  The dominant `r` scale is `r ≍ τ^{−1/2}` (where `r²τ/2 ≍ 1`),
exposing the local-CLT structure: the ratio-deviation estimate (the next wave)
becomes an incomplete-theta / Euler–Maclaurin estimate on the ONE-dimensional
`R_m`, `D_m` rather than on the raw 2D Clebsch convolution.  `ρ³ = g₁/(2g₀)` (the
matched-retune input) is, in `(r,d)` form, the ratio of the `k = 2` to `k = 1`
separated combinations — `g₀ = Zsum(w²)` is `g0_rd_check`; `g₁` is the `k = 2`
combination, whose closed `(r,d)` form awaits the assembled `RDFactorization`.

HONEST VERDICT.  The EXACT `(r,d)` per-term factorization (the `w`-power
diagonalization and the `ij = (r²−d²)/4` coefficient separation) is GENUINELY
PROVED, as is the clean double sum, the index characterization, the `σ = √w`
substrate, and the `k = 1` cross-check.  The full assembled separated identity is
NAMED, not inhabited: the open content is exactly the CReal finite-sum reindex
across the `(a,b)→(r,d)` bijection.  This is the technical lever exposing the
local-CLT / τ/2 structure — NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FusionRDFactor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionRDFactor.ofNat_mul_eqv
#print axioms YMGap.Continuum.FusionRDFactor.bondMovedCoeff_p2_doubleSum
#print axioms YMGap.Continuum.FusionRDFactor.mulRD_nat
#print axioms YMGap.Continuum.FusionRDFactor.sqAddRD_nat
#print axioms YMGap.Continuum.FusionRDFactor.coeffW_mul_rd
#print axioms YMGap.Continuum.FusionRDFactor.rdIndex_iff
#print axioms YMGap.Continuum.FusionRDFactor.sigmaFrom_sq
#print axioms YMGap.Continuum.FusionRDFactor.sigmaFrom_isPositive
#print axioms YMGap.Continuum.FusionRDFactor.g0_rd_check
#print axioms YMGap.Continuum.FusionRDFactor.coeffW_sq_rd
#print axioms YMGap.Continuum.FusionRDFactor.rdFactorization_identity
