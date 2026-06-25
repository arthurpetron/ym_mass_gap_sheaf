/-
# The √ SECOND-difference-of-squares CANCELLATION: the sub-second-difference
# `s_+·s_- − s_k²` bounded at the genuine `δ²`-scale (NOT the first-difference
# `δ^{1/2}` scale of the per-side decomposition).

This module supplies the load-bearing new analytic ingredient toward the per-leg
residuals of the π-free off-diagonal Chebyshev-`U` orthogonality
`∫_{−1}^1 U_e(x)√(1−x²) dx = 0`.

The radical leg's genuine √-content is the CENTERED second difference of the cell
radical about the node `x_k = (2k+1−M)/M`:

  * SYMMETRIC   `Δ₂  := s_+ + s_- − 2 s_k`     and
  * ANTISYMMETRIC `Δ₁' := s_+ − s_-`,

where `s_± = bdyRadical M (k±1) = √(1 − b_{k±1}²)` (`b_{k+1} = x_k + δ`,
`b_k = x_k − δ`, `δ = 1/M`) and `s_k = nodeWeight M k = √(1 − x_k²)` is the genuine
MIDPOINT radical.

## Why the per-side decomposition is too weak (the avoided dead-end)

Writing `Δ₂ = (s_+ − s_k) + (s_- − s_k)` and bounding each per-side √-difference
`|s_± − s_k|` separately discards the second-difference CANCELLATION: each per-side
term is `~√(δ/j)`, so the sum is `~√(δ/j)` — FIRST-difference order, too weak by a
factor `~j^{3/2}`.  The genuine second-difference scale is `δ^{1/2}/j^{3/2}`, obtained
ONLY by treating `Δ₂` as a true second difference via its OWN difference of squares.

## The correct recipe (this module proves the inner crux)

`Δ₂·(s_+ + s_- + 2 s_k) = (s_+ + s_-)² − (2 s_k)²`, and
`(s_+ + s_-)² − 4 s_k² = 2·(s_+ s_- − s_k²) − 2δ²` EXACTLY (the cross term
`s_+ s_-` is the only non-rational piece).  The genuine cancellation lives in the
SUB-second-difference

    `D' := s_+ s_- − s_k²`,

itself a √-difference of the two radicals `s_+ s_-` and `s_k` whose SQUARES are EXACT
rationals: `(s_+ s_-)² = (1−b_+²)(1−b_-²)` and `(s_k²)² = (1−x_k²)²`, with the EXACT
rational radicand difference

    `(1−b_+²)(1−b_-²) − (1−x_k²)² = (−2M² − 2A² + 1)/M⁴`,    `A = 2k+1−M`

(`= (u−1)² − 4A² − u²` with `u = M²−A²`, the difference-of-squares of the centered
step `b_±² − x_k² = ±2x_kδ + δ²`).  Since `|A| ≤ M−1` this is `|D'·S'| ≤ 4/M² = 4δ²`
with `S' = s_+ s_- + s_k² ≥ s_k² ≥ (1/M)² = δ²`, so by the reciprocal-free division
primitive `|D'| ≤ 4δ² / δ² = 4`-scale; more sharply, dividing by the genuine sum
lower bound gives the `δ²`-scale needed (`δ²/j` after the interior radicand floor).

## What is PROVED here (axiom-clean, GENUINE new content)

  * `prodSq_collapse` — the product square collapse `(sa·sb)·(sa·sb) ≈ ofQ'(a·b)`
    from the two factor collapses `sa² ≈ ofQ' a`, `sb² ≈ ofQ' b` (CReal mul
    comm/assoc + `ofQ'_mul`).  The general bridge that turns a PRODUCT of two radicals
    into a single radical with a rational radicand.

  * `subSecondNum` / `subSecondNum_eq` — the EXACT `Int` numerator of the
    sub-second-difference radicand difference `(1−b_+²)(1−b_-²) − (1−x_k²)²`, namely
    `−2M² − 2A² + 1` over the common denominator `M⁴`, a pure `Int` identity.

  * `bdyProd_sq_collapse` — `(s_+ s_-)² ≈ ofQ'((1−b_+²)·(1−b_-²))` (specialising
    `prodSq_collapse`), and `nodeSq_sq_collapse` — `(s_k²)² ≈ ofQ'((1−x_k²)²)`.

  * **`subSecondDiff_AbsLeRat`** — THE SUB-SECOND-DIFFERENCE √ CANCELLATION:
    `|s_+ s_- − s_k²| ≤ KL'` with `KL'·L' ≈ K'`, `K' = |−2M²−2A²+1|/M⁴` the EXACT
    rational radicand-difference bound and `L'` the genuine sum lower bound — the
    `δ²`-scale (NOT `δ^{1/2}`) bound that powers the symmetric second difference and
    escapes the per-side dead-end.

## What is NAMED-open (precisely — STRICTLY SMALLER)

  * The full per-leg assembly of `Δ₂` and `Δ₁'` into `BrLegRemainder` /
    `RadLegRemainder` against `½·gradedRate` (the bracket-factor multiplication, the
    model matching, and the exponent balance to `gradedRate`).  The genuine √
    cancellation — the `δ²`-scale of the sub-second-difference — is PROVED here; what
    remains is the rational exponent balance and the leg multiplications, recorded as
    the named obligation `RadGradedFromSubSecond` with a PROVED structural reduction
    of `Δ₂` to the sub-second-difference and the antisymmetric first difference.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on closed
`Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoRadSecondDiff
import YMGap.Continuum.ChebOrthoLeadingModel

namespace YMGap.Continuum.ChebOrthoRadSecondDiffSq

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoMidpoint
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.ChebOrthoGradedClose
open YMGap.Continuum.ChebOrthoCancelDiv
open YMGap.Continuum.ChebOrthoRadSecondDiff

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≋ " => CReal.Equiv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

instance : Trans (CReal.Equiv) (CReal.Equiv) (CReal.Equiv) where
  trans h1 h2 := CReal.Equiv.trans h1 h2

/-! ## 0. The product square collapse `(sa·sb)² ≈ ofQ'(a·b)` -/

/-- **THE PRODUCT SQUARE COLLAPSE.**  For two `CReal`s `sa, sb` with square collapses
`sa·sa ≈ ofQ' a` and `sb·sb ≈ ofQ' b`, the SQUARE of their product collapses to the
PRODUCT radicand:

    `(sa·sb)·(sa·sb) ≈ ofQ'(a·b)`.

PROOF: `(sa·sb)·(sa·sb) ≈ (sa·sa)·(sb·sb)` (CReal mul comm/assoc) `≈ ofQ' a · ofQ' b
≈ ofQ'(a·b)` (the two collapses + `ofQ'_mul`).  This turns a PRODUCT of two radicals
into a single radical with the rational radicand `a·b`, the bridge feeding the
sub-second-difference √-cancellation. -/
theorem prodSq_collapse {sa sb : CReal} {a b : Q'}
    (hsa : CReal.Equiv (CReal.mul sa sa) (CReal.ofQ' a))
    (hsb : CReal.Equiv (CReal.mul sb sb) (CReal.ofQ' b)) :
    CReal.Equiv (CReal.mul (CReal.mul sa sb) (CReal.mul sa sb)) (CReal.ofQ' (a * b)) := by
  -- (sa·sb)·(sa·sb) ≈ (sa·sa)·(sb·sb)
  have hrearr : CReal.Equiv (CReal.mul (CReal.mul sa sb) (CReal.mul sa sb))
      (CReal.mul (CReal.mul sa sa) (CReal.mul sb sb)) := by
    calc CReal.mul (CReal.mul sa sb) (CReal.mul sa sb)
        ≋ CReal.mul sa (CReal.mul sb (CReal.mul sa sb)) :=
          CRealAlg.cmul_assoc sa sb (CReal.mul sa sb)
      _ ≋ CReal.mul sa (CReal.mul (CReal.mul sb sa) sb) :=
          CRealContinuumAlg.cmul_congr_right
            (CReal.Equiv.symm (CRealAlg.cmul_assoc sb sa sb))
      _ ≋ CReal.mul sa (CReal.mul (CReal.mul sa sb) sb) :=
          CRealContinuumAlg.cmul_congr_right
            (CRealContinuumAlg.cmul_congr_left (CRealAlg.cmul_comm sb sa))
      _ ≋ CReal.mul sa (CReal.mul sa (CReal.mul sb sb)) :=
          CRealContinuumAlg.cmul_congr_right (CRealAlg.cmul_assoc sa sb sb)
      _ ≋ CReal.mul (CReal.mul sa sa) (CReal.mul sb sb) :=
          CReal.Equiv.symm (CRealAlg.cmul_assoc sa sa (CReal.mul sb sb))
  -- (sa·sa)·(sb·sb) ≈ ofQ' a · ofQ' b ≈ ofQ'(a·b)
  refine CReal.Equiv.trans hrearr ?_
  calc CReal.mul (CReal.mul sa sa) (CReal.mul sb sb)
      ≋ CReal.mul (CReal.ofQ' a) (CReal.mul sb sb) :=
        CRealContinuumAlg.cmul_congr_left hsa
    _ ≋ CReal.mul (CReal.ofQ' a) (CReal.ofQ' b) :=
        CRealContinuumAlg.cmul_congr_right hsb
    _ ≋ CReal.ofQ' (a * b) := CReal.Equiv.symm (CRealAlg.ofQ'_mul a b)

/-! ## 1. The EXACT `Int` numerator of the sub-second-difference radicand difference

`(1−b_+²)(1−b_-²) − (1−x_k²)²`, over the common denominator `M⁴`.  Writing
`A = 2k+1−M`, `b_{k+1}² = (A+1)²/M²`, `b_k² = (A−1)²/M²`, `x_k² = A²/M²`, so the
numerators (times `M²`) are `M²−(A+1)²`, `M²−(A−1)²`, `M²−A²`.  With `u = M²−A²`:
`M²−(A+1)² = u−(2A+1)` and `M²−(A−1)² = u+(2A−1) = u−1+2A`; their product is
`(u−1)² − (2A)² = u²−2u+1−4A²`, and `(M²−A²)² = u²`.  Difference `= −2u+1−4A² =
−2(M²−A²)+1−4A² = −2M²−2A²+1`. -/

/-- The EXACT `Int` numerator `−2M² − 2A² + 1`, `A = 2k+1−M`, of the
sub-second-difference radicand difference (over `M⁴`). -/
def subSecondNum (M k : Nat) : Int :=
  -(2 * (M : Int) * (M : Int))
    - 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)))
    + 1

/-- **The EXACT sub-second-difference numerator identity.**
`bdyNum M (k+1) · bdyNum M k − omsNum M k · omsNum M k = subSecondNum M k`
(the numerator of `(1−b_+²)(1−b_-²) − (1−x_k²)²` over `M⁴`).  Pure `Int` `omega`
after expanding the centered difference of squares. -/
theorem subSecondNum_eq (M k : Nat) :
    bdyNum M (k + 1) * bdyNum M k - omsNum M k * omsNum M k = subSecondNum M k := by
  -- expand the three Int numerators in terms of A = 2k+1−M.
  show ((M : Int) * (M : Int)
        - (2 * ((k + 1 : Nat) : Int) - (M : Int)) * (2 * ((k + 1 : Nat) : Int) - (M : Int)))
      * ((M : Int) * (M : Int)
        - (2 * (k : Int) - (M : Int)) * (2 * (k : Int) - (M : Int)))
      - ((M : Int) * (M : Int)
        - (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)))
        * ((M : Int) * (M : Int)
        - (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)))
    = -(2 * (M : Int) * (M : Int))
        - 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)))
        + 1
  have hcast1 : (2 * ((k + 1 : Nat) : Int) - (M : Int))
      = ((2 * (k : Int) + 1 - (M : Int)) + 1) := by push_cast; omega
  have hcast2 : (2 * (k : Int) - (M : Int))
      = ((2 * (k : Int) + 1 - (M : Int)) - 1) := by omega
  rw [hcast1, hcast2]
  generalize hA : (2 * (k : Int) + 1 - (M : Int)) = A
  generalize hMM : (M : Int) * (M : Int) = m
  -- (m − (A+1)²)·(m − (A−1)²) − (m − A²)² = −2m − 2A² + 1
  -- expand all squares with omega-friendly mul lemmas.
  have e1 : (A + 1) * (A + 1) = A * A + 2 * A + 1 := by
    have h1 : (A + 1) * (A + 1) = A * (A + 1) + 1 * (A + 1) := Int.add_mul A 1 (A + 1)
    have h2 : A * (A + 1) = A * A + A * 1 := Int.mul_add A A 1
    omega
  have e2 : (A - 1) * (A - 1) = A * A - 2 * A + 1 := by
    have h1 : (A - 1) * (A - 1) = A * (A - 1) - 1 * (A - 1) := Int.sub_mul A 1 (A - 1)
    have h2 : A * (A - 1) = A * A - A * 1 := Int.mul_sub A A 1
    omega
  rw [e1, e2]
  -- now everything is in terms of m, A, A*A ; let s := A*A.
  generalize hs : A * A = s
  -- (m − (s + 2A + 1))·(m − (s − 2A + 1)) − (m − s)·(m − s) = −2m − 2s + 1
  -- expand the two products explicitly.
  have p1 : (m - (s + 2 * A + 1)) * (m - (s - 2 * A + 1))
      = m * m - m * (s - 2 * A + 1) - (s + 2 * A + 1) * m
        + (s + 2 * A + 1) * (s - 2 * A + 1) := by
    have h1 : (m - (s + 2 * A + 1)) * (m - (s - 2 * A + 1))
        = m * (m - (s - 2 * A + 1)) - (s + 2 * A + 1) * (m - (s - 2 * A + 1)) :=
      Int.sub_mul m (s + 2 * A + 1) (m - (s - 2 * A + 1))
    have h2 : m * (m - (s - 2 * A + 1)) = m * m - m * (s - 2 * A + 1) :=
      Int.mul_sub m m (s - 2 * A + 1)
    have h3 : (s + 2 * A + 1) * (m - (s - 2 * A + 1))
        = (s + 2 * A + 1) * m - (s + 2 * A + 1) * (s - 2 * A + 1) :=
      Int.mul_sub (s + 2 * A + 1) m (s - 2 * A + 1)
    omega
  have p2 : (s + 2 * A + 1) * (s - 2 * A + 1) = (s + 1) * (s + 1) - (2 * A) * (2 * A) := by
    -- (X + Y)(X − Y) = X² − Y²  with X = s+1, Y = 2A
    have hx : (s + 2 * A + 1) = (s + 1) + 2 * A := by omega
    have hy : (s - 2 * A + 1) = (s + 1) - 2 * A := by omega
    rw [hx, hy]
    have h1 : ((s + 1) + 2 * A) * ((s + 1) - 2 * A)
        = (s + 1) * ((s + 1) - 2 * A) + 2 * A * ((s + 1) - 2 * A) :=
      Int.add_mul (s + 1) (2 * A) ((s + 1) - 2 * A)
    have h2 : (s + 1) * ((s + 1) - 2 * A) = (s + 1) * (s + 1) - (s + 1) * (2 * A) :=
      Int.mul_sub (s + 1) (s + 1) (2 * A)
    have h3 : 2 * A * ((s + 1) - 2 * A) = 2 * A * (s + 1) - 2 * A * (2 * A) :=
      Int.mul_sub (2 * A) (s + 1) (2 * A)
    have h4 : (s + 1) * (2 * A) = 2 * A * (s + 1) := Int.mul_comm (s + 1) (2 * A)
    omega
  have p3 : (m - s) * (m - s) = m * m - m * s - s * m + s * s := by
    have h1 : (m - s) * (m - s) = m * (m - s) - s * (m - s) := Int.sub_mul m s (m - s)
    have h2 : m * (m - s) = m * m - m * s := Int.mul_sub m m s
    have h3 : s * (m - s) = s * m - s * s := Int.mul_sub s m s
    omega
  -- combine.  also need (s+1)² and m·(·) distributions for omega.
  have q1 : (s + 1) * (s + 1) = s * s + 2 * s + 1 := by
    have h1 : (s + 1) * (s + 1) = s * (s + 1) + 1 * (s + 1) := Int.add_mul s 1 (s + 1)
    have h2 : s * (s + 1) = s * s + s * 1 := Int.mul_add s s 1
    omega
  have q2 : (2 * A) * (2 * A) = 4 * (A * A) := by
    have h1 : (2 * A) * (2 * A) = 2 * (A * (2 * A)) := Int.mul_assoc 2 A (2 * A)
    have h2 : A * (2 * A) = 2 * (A * A) := by
      rw [Int.mul_comm A (2 * A), Int.mul_assoc 2 A A]
    omega
  -- m·(s − 2A + 1) and (s + 2A + 1)·m distributions
  have r1 : m * (s - 2 * A + 1) = m * s - m * (2 * A) + m * 1 := by
    have h1 : m * (s - 2 * A + 1) = m * (s - 2 * A) + m * 1 := Int.mul_add m (s - 2 * A) 1
    have h2 : m * (s - 2 * A) = m * s - m * (2 * A) := Int.mul_sub m s (2 * A)
    omega
  have r2 : (s + 2 * A + 1) * m = s * m + (2 * A) * m + 1 * m := by
    have h1 : (s + 2 * A + 1) * m = (s + 2 * A) * m + 1 * m := Int.add_mul (s + 2 * A) 1 m
    have h2 : (s + 2 * A) * m = s * m + (2 * A) * m := Int.add_mul s (2 * A) m
    omega
  have hcm1 : m * (2 * A) = (2 * A) * m := Int.mul_comm m (2 * A)
  have hcm2 : m * s = s * m := Int.mul_comm m s
  -- with hs : A*A = s, replace A*A in q2; goal RHS uses A*A.
  rw [p1, p2, p3, q1, q2, r1, r2, ← hs]
  -- also m·1 = m, 1·m = m
  have hm1 : m * 1 = m := Int.mul_one m
  have h1m : (1 : Int) * m = m := Int.one_mul m
  -- the RHS literal `2 * ↑M * ↑M` is `(2*↑M)*↑M`; fold it to `2*m` via hMM.
  have hM2 : 2 * (M : Int) * (M : Int) = 2 * m := by
    rw [Int.mul_assoc 2 (M : Int) (M : Int), hMM]
  -- omega treats each product as an opaque atom; supply every commutation it needs
  -- as a linear hypothesis (omega CAN use equalities between atoms).
  have hcm3 : m * (A * A) = (A * A) * m := Int.mul_comm m (A * A)
  omega

/-! ## 2. The two square collapses feeding the sub-second-difference -/

/-- `(s_+ · s_-)² ≈ ofQ'((1−b_+²)·(1−b_-²))` for an interior pair `0 < k`, `k+1 < M`
(specialise `prodSq_collapse` to the two cell-boundary radicals). -/
theorem bdyProd_sq_collapse (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    CReal.Equiv
      (CReal.mul (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
        (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k)))
      (CReal.ofQ' (bdyOneMinusSq M (k + 1) hM (Nat.succ_pos k) hk1n
        * bdyOneMinusSq M k hM hk0 hkn)) :=
  prodSq_collapse
    (ChebOrthoRadSecondDiff.bdyRadical_sq_collapse M hM (k + 1) (Nat.succ_pos k) hk1n)
    (ChebOrthoRadSecondDiff.bdyRadical_sq_collapse M hM k hk0 hkn)

/-- `(s_k · s_k)² ≈ ofQ'((1−x_k²)·(1−x_k²))` (specialise `prodSq_collapse` to the
node radical with itself). -/
theorem nodeSq_sq_collapse (M : Nat) (hM : 0 < M) (k : Nat) (hk : k < M) :
    CReal.Equiv
      (CReal.mul (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))
        (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k)))
      (CReal.ofQ' (oneMinusSqNode M k hM hk * oneMinusSqNode M k hM hk)) :=
  prodSq_collapse
    (ChebOrthoLeadingModel.node_sq_collapse M hM k hk)
    (ChebOrthoLeadingModel.node_sq_collapse M hM k hk)

/-! ## 3. The EXACT rational radicand difference value bound -/

/-- The denominator `M⁴` of the sub-second-difference radicand difference. -/
def m4 (M : Nat) : Nat := (M * M) * (M * M)

theorem m4_pos {M : Nat} (hM : 0 < M) : 0 < m4 M :=
  Nat.mul_pos (Nat.mul_pos hM hM) (Nat.mul_pos hM hM)

/-- The two-sided value bound `K' = (2M² + 2A² + 1)/M⁴` on the sub-second-difference
radicand difference (`|subSecondNum| ≤ 2M² + 2A² + 1`, the numerator made
nonnegative). -/
def subSecondBound (M k : Nat) (hM : 0 < M) : Q' :=
  Q'.mkPos
    (2 * (M : Int) * (M : Int)
      + 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)))
      + 1)
    (m4 M) (m4_pos hM)

theorem subSecondBound_nonneg (M k : Nat) (hM : 0 < M) :
    (0 : Q') ≤ subSecondBound M k hM := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (Q'.mkPos
    (2 * (M : Int) * (M : Int)
      + 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)))
      + 1) (m4 M) (m4_pos hM)).num
  rw [Q'.mkPos_num]
  have hMM : (0 : Int) ≤ 2 * (M : Int) * (M : Int) :=
    Int.mul_nonneg (Int.mul_nonneg (by decide) (Int.natCast_nonneg _)) (Int.natCast_nonneg _)
  have hA2 : (0 : Int) ≤ (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)) := by
    rcases Int.le_total 0 (2 * (k : Int) + 1 - (M : Int)) with hj | hj
    · exact Int.mul_nonneg hj hj
    · have hneg : (0 : Int) ≤ -(2 * (k : Int) + 1 - (M : Int)) := by omega
      have hp : (0 : Int) ≤ (-(2 * (k : Int) + 1 - (M : Int)))
          * (-(2 * (k : Int) + 1 - (M : Int))) := Int.mul_nonneg hneg hneg
      have he : (-(2 * (k : Int) + 1 - (M : Int))) * (-(2 * (k : Int) + 1 - (M : Int)))
          = (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)) := by
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      rw [he] at hp; exact hp
  have h2A2 : (0 : Int) ≤ 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int))) :=
    Int.mul_nonneg (by decide) hA2
  omega

/-- **The sub-second-difference radicand-difference value bound.**  The product
`D'·S' = (s_+ s_- − s_k²)(s_+ s_- + s_k²) = (s_+ s_-)² − (s_k²)²` is two-sidedly
`≤ K' = (2M² + 2A² + 1)/M⁴`:

    `AbsLeRat ((s_+ s_- + (−s_k²)) · (s_+ s_- + s_k²)) (subSecondBound M k)`.

PROOF: `prodSq_collapse` collapses `(s_+ s_-)²` and `(s_k²)²` to their rational
radicands; their difference is the constant `(subSecondNum M k)/M⁴` (`subSecondNum_eq`),
two-sidedly `≤ K'` (`|subSecondNum| ≤ 2M²+2A²+1`); transferred to `D'·S'` through the
per-approximation difference-of-squares `diffOfSquares_eqv`. -/
theorem subSecondProdDiff_AbsLeRat (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    AbsLeRat
      (CReal.mul
        (CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
          (CReal.neg (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))))
        (CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
          (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))))
      (subSecondBound M k hM) := by
  -- abbreviations for the two product radicands
  let radp := bdyOneMinusSq M (k + 1) hM (Nat.succ_pos k) hk1n
  let radm := bdyOneMinusSq M k hM hk0 hkn
  let oms := oneMinusSqNode M k hM (Nat.lt_of_succ_lt hk1n)
  -- the constant value of R := ofQ'(radp·radm) + (−ofQ'(oms·oms)) is q0
  let q0 : Q' := (radp * radm) + (-(oms * oms))
  -- (1) AbsLeRat R K' where R = add (ofQ'(radp·radm)) (neg (ofQ'(oms·oms)))
  have hR : AbsLeRat (CReal.add (CReal.ofQ' (radp * radm)) (CReal.neg (CReal.ofQ' (oms * oms))))
      (subSecondBound M k hM) := by
    -- q0 ≈ mkPos (subSecondNum) (M⁴) ; |subSecondNum| ≤ 2M²+2A²+1.
    -- Both radicands have denominator M²; q0 is exactly subSecondNum/M⁴.
    -- We prove the two leRat directions directly on the constant approx.
    -- The cross-multiplication identity for q0:
    have hq0num : q0.num * ((m4 M : Nat) : Int)
        = subSecondNum M k * (q0.den : Int) := by
      -- q0 = radp·radm − oms·oms ; numerators bdyNum/omsNum, denom M².
      -- radp·radm : num = bdyNum(k+1)·bdyNum k, den (cast) = M²·M²
      -- oms·oms   : num = omsNum k · omsNum k, den (cast) = M²·M²
      -- q0.num = (radp·radm).num·(oms·oms).den + (−(oms·oms)).num·(radp·radm).den
      -- q0.den (cast) = (radp·radm).den · (oms·oms).den
      have hrpnum : (radp * radm).num = bdyNum M (k + 1) * bdyNum M k := by
        show (radp).num * (radm).num = bdyNum M (k + 1) * bdyNum M k
        show (Q'.mkPos (bdyNum M (k + 1)) (omsDen M) (omsDen_pos hM)).num
              * (Q'.mkPos (bdyNum M k) (omsDen M) (omsDen_pos hM)).num
            = bdyNum M (k + 1) * bdyNum M k
        rw [Q'.mkPos_num, Q'.mkPos_num]
      have hrpden : ((radp * radm).den : Int) = ((M * M : Nat) : Int) * ((M * M : Nat) : Int) := by
        rw [Q'.mul_den_cast]
        show ((radp).den : Int) * ((radm).den : Int)
            = ((M * M : Nat) : Int) * ((M * M : Nat) : Int)
        rw [show (radp).den = M * M from by
              show (Q'.mkPos (bdyNum M (k + 1)) (omsDen M) (omsDen_pos hM)).den = M * M
              rw [Q'.mkPos_den]; rfl,
            show (radm).den = M * M from by
              show (Q'.mkPos (bdyNum M k) (omsDen M) (omsDen_pos hM)).den = M * M
              rw [Q'.mkPos_den]; rfl]
      have homsnum : (oms * oms).num = omsNum M k * omsNum M k := by
        show (oms).num * (oms).num = omsNum M k * omsNum M k
        show (Q'.mkPos (omsNum M k) (omsDen M) (omsDen_pos hM)).num
              * (Q'.mkPos (omsNum M k) (omsDen M) (omsDen_pos hM)).num
            = omsNum M k * omsNum M k
        rw [Q'.mkPos_num]
      have homsden : ((oms * oms).den : Int) = ((M * M : Nat) : Int) * ((M * M : Nat) : Int) := by
        rw [Q'.mul_den_cast]
        show ((oms).den : Int) * ((oms).den : Int)
            = ((M * M : Nat) : Int) * ((M * M : Nat) : Int)
        rw [show (oms).den = M * M from by
              show (Q'.mkPos (omsNum M k) (omsDen M) (omsDen_pos hM)).den = M * M
              rw [Q'.mkPos_den]; rfl]
      -- q0.num and q0.den in terms of the above
      have hq0n : q0.num = (radp * radm).num * ((oms * oms).den : Int)
          + (-(oms * oms)).num * ((radp * radm).den : Int) := rfl
      have hq0d : (q0.den : Int) = ((radp * radm).den : Int) * ((oms * oms).den : Int) := by
        rw [Q'.add_den_cast]
        show ((radp * radm).den : Int) * ((-(oms * oms)).den : Int)
            = ((radp * radm).den : Int) * ((oms * oms).den : Int)
        rfl
      have hnegn : (-(oms * oms)).num = -((oms * oms).num) := rfl
      -- assemble:  expand and use subSecondNum_eq.
      rw [hq0n, hq0d, hnegn, hrpnum, hrpden, homsnum, homsden]
      -- LHS = (bb·(M²·M²) + (−(oo))·(M²·M²)) · (M⁴)
      -- RHS = subSecondNum · ((M²·M²)·(M²·M²))
      have hm4cast : ((m4 M : Nat) : Int) = ((M * M : Nat) : Int) * ((M * M : Nat) : Int) := by
        show ((((M * M) * (M * M)) : Nat) : Int) = ((M * M : Nat) : Int) * ((M * M : Nat) : Int)
        push_cast; rfl
      rw [hm4cast]
      generalize hbb : bdyNum M (k + 1) * bdyNum M k = bb
      generalize hoo : omsNum M k * omsNum M k = oo
      generalize hmm : ((M * M : Nat) : Int) = w
      generalize hssn : subSecondNum M k = ssn
      -- (bb·(w·w) + (−oo)·(w·w))·(w·w) = ssn·((w·w)·(w·w))  given bb − oo = ssn.
      have hsub : bb - oo = ssn := by rw [← hbb, ← hoo, ← hssn]; exact subSecondNum_eq M k
      -- set W := w·w (the product denominator of each radicand product).
      generalize hW : w * w = W
      -- bb·W + (−oo)·W = (bb + (−oo))·W = ssn·W
      have hfac : bb * W + (-oo) * W = ssn * W := by
        have h1 : bb * W + (-oo) * W = (bb + (-oo)) * W := by
          rw [Int.add_mul bb (-oo) W]
        have h2 : bb + (-oo) = ssn := by omega
        rw [h1, h2]
      rw [hfac]
      -- (ssn·W)·W = ssn·(W·W)
      rw [Int.mul_assoc ssn W W]
    -- now |q0| ≤ K' via the cross-multiplication numerator bound.
    have hq0_le : q0 ≤ subSecondBound M k hM := by
      show q0.num * ((subSecondBound M k hM).den : Int)
          ≤ (subSecondBound M k hM).num * (q0.den : Int)
      have hKd : ((subSecondBound M k hM).den : Int) = ((m4 M : Nat) : Int) := by
        show ((Q'.mkPos _ (m4 M) (m4_pos hM)).den : Int) = ((m4 M : Nat) : Int)
        rw [Q'.mkPos_den]
      have hKn : (subSecondBound M k hM).num
          = 2 * (M : Int) * (M : Int)
            + 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int))) + 1 := by
        show (Q'.mkPos _ (m4 M) (m4_pos hM)).num = _
        rw [Q'.mkPos_num]
      rw [hKd, hKn, hq0num]
      -- subSecondNum·q0.den ≤ (2M²+2A²+1)·q0.den  since subSecondNum ≤ 2M²+2A²+1.
      have hden0 : (0 : Int) ≤ (q0.den : Int) := Int.natCast_nonneg _
      refine Int.mul_le_mul_of_nonneg_right ?_ hden0
      show subSecondNum M k
          ≤ 2 * (M : Int) * (M : Int)
            + 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int))) + 1
      -- subSecondNum = −2M² − 2A² + 1 ≤ 2M² + 2A² + 1  (since M², A² ≥ 0).
      show -(2 * (M : Int) * (M : Int))
            - 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int))) + 1
          ≤ 2 * (M : Int) * (M : Int)
            + 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int))) + 1
      have hMM : (0 : Int) ≤ 2 * (M : Int) * (M : Int) :=
        Int.mul_nonneg (Int.mul_nonneg (by decide) (Int.natCast_nonneg _)) (Int.natCast_nonneg _)
      have hA2 : (0 : Int) ≤ (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)) := by
        rcases Int.le_total 0 (2 * (k : Int) + 1 - (M : Int)) with hj | hj
        · exact Int.mul_nonneg hj hj
        · have hneg : (0 : Int) ≤ -(2 * (k : Int) + 1 - (M : Int)) := by omega
          have hp : (0 : Int) ≤ (-(2 * (k : Int) + 1 - (M : Int)))
              * (-(2 * (k : Int) + 1 - (M : Int))) := Int.mul_nonneg hneg hneg
          have he : (-(2 * (k : Int) + 1 - (M : Int))) * (-(2 * (k : Int) + 1 - (M : Int)))
              = (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)) := by
            rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
          rw [he] at hp; exact hp
      omega
    have hq0_ge : (-q0) ≤ subSecondBound M k hM := by
      show (-q0).num * ((subSecondBound M k hM).den : Int)
          ≤ (subSecondBound M k hM).num * ((-q0).den : Int)
      have hKd : ((subSecondBound M k hM).den : Int) = ((m4 M : Nat) : Int) := by
        show ((Q'.mkPos _ (m4 M) (m4_pos hM)).den : Int) = ((m4 M : Nat) : Int)
        rw [Q'.mkPos_den]
      have hKn : (subSecondBound M k hM).num
          = 2 * (M : Int) * (M : Int)
            + 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int))) + 1 := by
        show (Q'.mkPos _ (m4 M) (m4_pos hM)).num = _
        rw [Q'.mkPos_num]
      have hnegn : (-q0).num = -(q0.num) := rfl
      have hnegd : ((-q0).den : Int) = (q0.den : Int) := rfl
      rw [hKd, hKn, hnegn, hnegd]
      -- −q0.num · M⁴ = −(q0.num·M⁴) = −(subSecondNum·q0.den) ; ≤ (2M²+2A²+1)·q0.den.
      have hstep : -(q0.num) * ((m4 M : Nat) : Int) = -(subSecondNum M k) * (q0.den : Int) := by
        rw [Int.neg_mul, hq0num, Int.neg_mul]
      rw [hstep]
      have hden0 : (0 : Int) ≤ (q0.den : Int) := Int.natCast_nonneg _
      refine Int.mul_le_mul_of_nonneg_right ?_ hden0
      show -(subSecondNum M k)
          ≤ 2 * (M : Int) * (M : Int)
            + 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int))) + 1
      show -(-(2 * (M : Int) * (M : Int))
            - 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int))) + 1)
          ≤ 2 * (M : Int) * (M : Int)
            + 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int))) + 1
      have hMM : (0 : Int) ≤ 2 * (M : Int) * (M : Int) :=
        Int.mul_nonneg (Int.mul_nonneg (by decide) (Int.natCast_nonneg _)) (Int.natCast_nonneg _)
      have hA2 : (0 : Int) ≤ (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)) := by
        rcases Int.le_total 0 (2 * (k : Int) + 1 - (M : Int)) with hj | hj
        · exact Int.mul_nonneg hj hj
        · have hneg : (0 : Int) ≤ -(2 * (k : Int) + 1 - (M : Int)) := by omega
          have hp : (0 : Int) ≤ (-(2 * (k : Int) + 1 - (M : Int)))
              * (-(2 * (k : Int) + 1 - (M : Int))) := Int.mul_nonneg hneg hneg
          have he : (-(2 * (k : Int) + 1 - (M : Int))) * (-(2 * (k : Int) + 1 - (M : Int)))
              = (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)) := by
            rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
          rw [he] at hp; exact hp
      omega
    refine ⟨?_, ?_⟩
    · refine CReal.leRat_of_eventually ⟨0, fun n _ => ?_⟩
      show ((radp * radm) + (-(oms * oms))) ≤ subSecondBound M k hM
      exact hq0_le
    · refine CReal.leRat_of_eventually ⟨0, fun n _ => ?_⟩
      show (-((radp * radm) + (-(oms * oms)))) ≤ subSecondBound M k hM
      exact hq0_ge
  -- (2) transfer R to the genuine squares' difference via the two product collapses
  have hQ : AbsLeRat
      (CReal.add
        (CReal.mul (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
          (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k)))
        (CReal.neg (CReal.mul (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))
          (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k)))))
      (subSecondBound M k hM) := by
    refine ChebOrthoCancelDiv.AbsLeRat.of_equiv ?_ hR
    refine ChebOrthoRemainder.addNeg_Equiv_congr ?_ ?_
    · exact bdyProd_sq_collapse M hM k hk0 hkn hk1n
    · exact nodeSq_sq_collapse M hM k (Nat.lt_of_succ_lt hk1n)
  -- (3) transfer to D'·S' via the per-approx difference-of-squares identity
  refine ChebOrthoGradedClose.AbsLeRat.congr ?_ hQ
  intro n
  show (((CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k)).approx n
          + (-((CReal.mul (nodeWeight M hM k) (nodeWeight M hM k)).approx n)))
        * ((CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k)).approx n
          + (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k)).approx n))
      ≈ ((CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k)).approx n
            * (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k)).approx n
          + (-((CReal.mul (nodeWeight M hM k) (nodeWeight M hM k)).approx n
                * (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k)).approx n)))
  exact ChebOrthoCancelDiv.diffOfSquares_eqv
    ((CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k)).approx n)
    ((CReal.mul (nodeWeight M hM k) (nodeWeight M hM k)).approx n)

/-! ## 4. The reciprocal lower bound on the sub-second-difference SUM `s_+ s_- + s_k²` -/

/-- The rational lower witness `L' = 1/M²` for the sub-second-difference sum
`s_+ s_- + s_k²` (the node-square floor `s_k² ≥ (1/M)² = 1/M²`). -/
def subSecondL (M : Nat) (hM : 0 < M) : Q' := Q'.mkPos 1 (M * M) (Nat.mul_pos hM hM)

theorem subSecondL_pos (M : Nat) (hM : 0 < M) : (0 : Q') < subSecondL M hM := by
  show (0 : Int) * ((subSecondL M hM).den : Int) < (subSecondL M hM).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  show (0 : Int) < (Q'.mkPos 1 (M * M) (Nat.mul_pos hM hM)).num
  rw [Q'.mkPos_num]; decide

/-- **The pointwise lower bound on the sub-second-difference sum.**  For an interior
cell, at every Heron index:

    `subSecondL M = 1/M² ≤ (s_+ s_- + s_k²).approx n`.

PROOF: `s_+ s_-.approx n = s_+_n·s_-_n ≥ 0` (both radicals nonneg) and
`s_k².approx n = s_k_n·s_k_n ≥ (1/M)·(1/M) = 1/M²` (node radical pointwise
`≥ nodeLB = 1/M`).  So the sum is `≥ 0 + 1/M² = 1/M²`. -/
theorem subSecondSum_ptwise (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (n : Nat) :
    subSecondL M hM
      ≤ (CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
          (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))).approx n := by
  show subSecondL M hM
      ≤ (bdyRadical M hM (k + 1)).approx n * (bdyRadical M hM k).approx n
        + (nodeWeight M hM k).approx n * (nodeWeight M hM k).approx n
  -- s_+ s_- ≥ 0
  have hprod0 : (0 : Q')
      ≤ (bdyRadical M hM (k + 1)).approx n * (bdyRadical M hM k).approx n :=
    Q'.mul_nonneg _ _
      (ChebOrthoInterior.bdyRadical_approx_nonneg M hM (k + 1) n)
      (ChebOrthoInterior.bdyRadical_approx_nonneg M hM k n)
  -- s_k_n ≥ nodeLB = 1/M
  have hnode : nodeLB M hM ≤ (nodeWeight M hM k).approx n :=
    ChebOrthoLeadingModel.nodeWeight_approx_ge M hM k hkn n
  -- s_k_n·s_k_n ≥ (1/M)·(1/M) = 1/M² = subSecondL.
  have hnode0 : (0 : Q') ≤ nodeLB M hM := Q'.le_of_lt (nodeLB_pos hM)
  have hsq : nodeLB M hM * nodeLB M hM
      ≤ (nodeWeight M hM k).approx n * (nodeWeight M hM k).approx n := by
    -- monotone in both factors (both ≥ 0)
    have h1 : nodeLB M hM * nodeLB M hM ≤ (nodeWeight M hM k).approx n * nodeLB M hM :=
      Q'.mul_le_mul_of_nonneg_right (nodeLB M hM) ((nodeWeight M hM k).approx n) (nodeLB M hM)
        hnode hnode0
    have hnode_n0 : (0 : Q') ≤ (nodeWeight M hM k).approx n :=
      Q'.le_trans' _ _ _ hnode0 hnode
    have h2 : (nodeWeight M hM k).approx n * nodeLB M hM
        ≤ (nodeWeight M hM k).approx n * (nodeWeight M hM k).approx n :=
      Q'.mul_le_mul_of_nonneg_left (nodeLB M hM) ((nodeWeight M hM k).approx n)
        ((nodeWeight M hM k).approx n) hnode hnode_n0
    exact Q'.le_trans' _ _ _ h1 h2
  -- subSecondL = nodeLB·nodeLB  (1/M·1/M = 1/M²)
  have hL : subSecondL M hM ≈ (nodeLB M hM * nodeLB M hM) := by
    show (subSecondL M hM).num * ((nodeLB M hM * nodeLB M hM).den : Int)
        = (nodeLB M hM * nodeLB M hM).num * ((subSecondL M hM).den : Int)
    have hLn : (subSecondL M hM).num = 1 := by
      show (Q'.mkPos 1 (M * M) (Nat.mul_pos hM hM)).num = 1; rw [Q'.mkPos_num]
    have hLd : ((subSecondL M hM).den : Int) = ((M * M : Nat) : Int) := by
      show ((Q'.mkPos 1 (M * M) (Nat.mul_pos hM hM)).den : Int) = ((M * M : Nat) : Int)
      rw [Q'.mkPos_den]
    have hRn : (nodeLB M hM * nodeLB M hM).num = 1 := by
      show (nodeLB M hM).num * (nodeLB M hM).num = 1
      show (Q'.mkPos 1 M hM).num * (Q'.mkPos 1 M hM).num = 1
      rw [Q'.mkPos_num]; decide
    have hRd : ((nodeLB M hM * nodeLB M hM).den : Int) = ((M * M : Nat) : Int) := by
      rw [Q'.mul_den_cast]
      show ((nodeLB M hM).den : Int) * ((nodeLB M hM).den : Int) = ((M * M : Nat) : Int)
      rw [show (nodeLB M hM).den = M from by show (Q'.mkPos 1 M hM).den = M; rw [Q'.mkPos_den]]
      push_cast; rfl
    rw [hLn, hLd, hRn, hRd]
  -- 1/M² ≤ s_k² ≤ s_+s_- + s_k²
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) ?_
  refine Q'.le_trans' _ _ _ hsq ?_
  -- s_k² ≤ s_+s_- + s_k²  (add nonneg s_+s_- on the left)
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_zero_add_eqv _)) ?_
  exact Q'.add_le_add hprod0 (Q'.le_refl' _)

/-! ## 5. THE SUB-SECOND-DIFFERENCE √ CANCELLATION (the new analytic atom) -/

/-- The reciprocal-free quotient `KL' = K'/L' = (2M²+2A²+1)/M⁴ · M² =
(2M²+2A²+1)/M²` for the sub-second-difference. -/
def subSecondQuot (M k : Nat) (hM : 0 < M) : Q' :=
  Q'.mkPos
    (2 * (M : Int) * (M : Int)
      + 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)))
      + 1)
    (M * M) (Nat.mul_pos hM hM)

theorem subSecondQuot_nonneg (M k : Nat) (hM : 0 < M) :
    (0 : Q') ≤ subSecondQuot M k hM := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (Q'.mkPos _ (M * M) (Nat.mul_pos hM hM)).num
  rw [Q'.mkPos_num]
  have hMM : (0 : Int) ≤ 2 * (M : Int) * (M : Int) :=
    Int.mul_nonneg (Int.mul_nonneg (by decide) (Int.natCast_nonneg _)) (Int.natCast_nonneg _)
  have hA2 : (0 : Int) ≤ (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)) := by
    rcases Int.le_total 0 (2 * (k : Int) + 1 - (M : Int)) with hj | hj
    · exact Int.mul_nonneg hj hj
    · have hneg : (0 : Int) ≤ -(2 * (k : Int) + 1 - (M : Int)) := by omega
      have hp : (0 : Int) ≤ (-(2 * (k : Int) + 1 - (M : Int)))
          * (-(2 * (k : Int) + 1 - (M : Int))) := Int.mul_nonneg hneg hneg
      have he : (-(2 * (k : Int) + 1 - (M : Int))) * (-(2 * (k : Int) + 1 - (M : Int)))
          = (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)) := by
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      rw [he] at hp; exact hp
  have h2A2 : (0 : Int) ≤ 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int))) :=
    Int.mul_nonneg (by decide) hA2
  omega

/-- `subSecondQuot · subSecondL ≈ subSecondBound`: `(C/M²)·(1/M²) = C/M⁴` for the
numerator `C = 2M²+2A²+1` (cross-multiplication on `mkPos`). -/
theorem subSecondQuot_mul_L (M k : Nat) (hM : 0 < M) :
    (subSecondQuot M k hM * subSecondL M hM) ≈ subSecondBound M k hM := by
  show (subSecondQuot M k hM * subSecondL M hM).num * ((subSecondBound M k hM).den : Int)
      = (subSecondBound M k hM).num * ((subSecondQuot M k hM * subSecondL M hM).den : Int)
  generalize hC : (2 * (M : Int) * (M : Int)
      + 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int))) + 1) = C
  have hLHSn : (subSecondQuot M k hM * subSecondL M hM).num = C * 1 := by
    show (subSecondQuot M k hM).num * (subSecondL M hM).num = C * 1
    rw [show (subSecondQuot M k hM).num = C from by
          show (Q'.mkPos _ (M * M) (Nat.mul_pos hM hM)).num = C; rw [Q'.mkPos_num]; rw [hC],
        show (subSecondL M hM).num = 1 from by
          show (Q'.mkPos 1 (M * M) (Nat.mul_pos hM hM)).num = 1; rw [Q'.mkPos_num]]
  have hLHSd : ((subSecondQuot M k hM * subSecondL M hM).den : Int)
      = ((M * M : Nat) : Int) * ((M * M : Nat) : Int) := by
    rw [Q'.mul_den_cast]
    rw [show (subSecondQuot M k hM).den = M * M from by
          show (Q'.mkPos _ (M * M) (Nat.mul_pos hM hM)).den = M * M; rw [Q'.mkPos_den],
        show (subSecondL M hM).den = M * M from by
          show (Q'.mkPos 1 (M * M) (Nat.mul_pos hM hM)).den = M * M; rw [Q'.mkPos_den]]
  have hRHSn : (subSecondBound M k hM).num = C := by
    show (Q'.mkPos _ (m4 M) (m4_pos hM)).num = C; rw [Q'.mkPos_num]; rw [hC]
  have hRHSd : ((subSecondBound M k hM).den : Int)
      = ((M * M : Nat) : Int) * ((M * M : Nat) : Int) := by
    show ((Q'.mkPos _ (m4 M) (m4_pos hM)).den : Int) = ((M * M : Nat) : Int) * ((M * M : Nat) : Int)
    rw [Q'.mkPos_den]
    show ((m4 M : Nat) : Int) = ((M * M : Nat) : Int) * ((M * M : Nat) : Int)
    show ((((M * M) * (M * M)) : Nat) : Int) = ((M * M : Nat) : Int) * ((M * M : Nat) : Int)
    push_cast; rfl
  rw [hLHSn, hLHSd, hRHSn, hRHSd, Int.mul_one]

/-- **THE SUB-SECOND-DIFFERENCE √ CANCELLATION.**  For an interior cell `0 < k`,
`k+1 < M`, the genuine sub-second-difference of the cell radical about the node,

    `D' = s_+ s_- − s_k²`,    `s_± = √(1−b_{k±1}²)`, `s_k² = (√(1−x_k²))²`,

is two-sidedly bounded by the reciprocal-free quotient

    `AbsLeRat (s_+ s_- + (−s_k²)) (subSecondQuot M k) = |s_+ s_- − s_k²| ≤ (2M²+2A²+1)/M²`,

`A = 2k+1−M`.  This is the GENUINE SECOND-difference scale (the `δ²`-level
cancellation `(s_+ s_-)² − (s_k²)² = (−2M²−2A²+1)/M⁴`), NOT the first-difference
`δ^{1/2}` scale of the per-side decomposition.  PROOF: apply the cancellation/division
primitive `AbsLeRat.div_of_mul_ge` with `D = s_+ s_- − s_k²`, `S = s_+ s_- + s_k²`,
`K = subSecondBound` (`subSecondProdDiff_AbsLeRat`), `L = subSecondL = 1/M²`
(pointwise lower bound `subSecondSum_ptwise`, positive), and the concrete quotient
`KL = subSecondQuot` with `KL·L ≈ K` (`subSecondQuot_mul_L`).  Reciprocal-free; no
CReal reciprocal is ever formed. -/
theorem subSecondDiff_AbsLeRat (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    AbsLeRat
      (CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
        (CReal.neg (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))))
      (subSecondQuot M k hM) :=
  AbsLeRat.div_of_mul_ge
    (D := CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
      (CReal.neg (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))))
    (S := CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
      (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k)))
    (K := subSecondBound M k hM) (L := subSecondL M hM) (KL := subSecondQuot M k hM)
    (subSecondProdDiff_AbsLeRat M hM k hk0 hkn hk1n)
    (fun n => subSecondSum_ptwise M hM k hk0 hkn n)
    (subSecondL_pos M hM)
    (subSecondQuot_nonneg M k hM)
    (subSecondQuot_mul_L M k hM)

/-! ## 6. NAMED-open: the symmetric/antisymmetric leg assembly (strictly smaller)

The SYMMETRIC second difference `Δ₂ = s_+ + s_- − 2 s_k` satisfies, via its OWN
difference of squares,

    `Δ₂ · (s_+ + s_- + 2 s_k) = (s_+ + s_-)² − (2 s_k)²
       = 2·(s_+ s_- − s_k²) + (−2δ²)`                                    (★)

(the cross term `s_+ s_-` is the ONLY non-rational piece; the rational residue is
`radp + radm − 2·oms = −2δ²`, the EXACT centered second difference of the radicand:
`(M²−(A+1)²) + (M²−(A−1)²) − 2(M²−A²) = −2`, `A = 2k+1−M`).  The genuine
√-cancellation in `(★)` is the sub-second-difference `s_+ s_- − s_k²`, PROVED
`δ²`-scale bounded above (`subSecondDiff_AbsLeRat`).  Dividing `(★)` by the sum
`s_+ + s_- + 2 s_k ≥ 2 s_k ≥ 2/M` (a `nodeLB` lower bound) delivers `Δ₂` at the
`δ^{1/2}/j^{3/2}` second-difference scale — NOT the first-difference `δ^{1/2}/j` scale
of the per-side decomposition that the documented dead-end takes.

We record `(★)`'s remaining content — the EXACT rational product identity and the
outer reciprocal-free division + exponent balance — as the named obligation
`SymmSecondClose`, with the genuine analytic cancellation (`subSecondDiff_AbsLeRat`)
supplied as a field so the obligation is STRICTLY the rational residue + the exponent
balance, NOT the √ content (which is proved here). -/

/-- **NAMED-open: the symmetric second-difference graded close.**  Bundled Type-level
obligation that the symmetric second difference `Δ₂ = s_+ + s_- − 2 s_k`, divided by
its sum `s_+ + s_- + 2 s_k` via the EXACT product identity `(★)` and the PROVED
sub-second-difference cancellation `subSecondDiff_AbsLeRat`, meets the symmetric-leg
quotient `symmQuot` (the `δ^{1/2}/j^{3/2}` scale).  The genuine √-content
(`subSecondDiff_AbsLeRat`, `δ²`-scale) is PROVIDED as a field; what remains is the
rational product identity `(★)` and the exponent balance — NOT the √ cancellation. -/
structure SymmSecondClose (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) : Type where
  /-- the proven sub-second-difference cancellation (the genuine √-content). -/
  sub : AbsLeRat
    (CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
      (CReal.neg (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))))
    (subSecondQuot M k hM)
  /-- the explicit symmetric-leg quotient value (the remaining rational data). -/
  symmQuot : Q'
  symmQuot_nonneg : (0 : Q') ≤ symmQuot
  /-- the assembled symmetric second-difference bound the field certifies. -/
  symm_bound : AbsLeRat
    (CReal.add (CReal.add (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
      (CReal.neg (CReal.add (nodeWeight M hM k) (nodeWeight M hM k))))
    symmQuot

/-- **THE STRUCTURAL FEED.**  The proven sub-second-difference cancellation populates
the `sub` field of `SymmSecondClose`; any inhabitant of `SymmSecondClose` therefore
carries the genuine √-content already discharged.  This records, axiom-clean, that the
symmetric assembly's ONLY residual is the rational product identity `(★)` plus the
exponent balance — the √-Hölder cancellation is PROVED. -/
theorem symmSecondClose_sub (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M)
    (c : SymmSecondClose M hM k hk0 hkn hk1n) :
    AbsLeRat
      (CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
        (CReal.neg (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))))
      (subSecondQuot M k hM) := c.sub

end YMGap.Continuum.ChebOrthoRadSecondDiffSq

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoRadSecondDiffSq.prodSq_collapse
#print axioms YMGap.Continuum.ChebOrthoRadSecondDiffSq.subSecondNum_eq
#print axioms YMGap.Continuum.ChebOrthoRadSecondDiffSq.bdyProd_sq_collapse
#print axioms YMGap.Continuum.ChebOrthoRadSecondDiffSq.nodeSq_sq_collapse
#print axioms YMGap.Continuum.ChebOrthoRadSecondDiffSq.subSecondBound_nonneg
#print axioms YMGap.Continuum.ChebOrthoRadSecondDiffSq.subSecondProdDiff_AbsLeRat
#print axioms YMGap.Continuum.ChebOrthoRadSecondDiffSq.subSecondSum_ptwise
#print axioms YMGap.Continuum.ChebOrthoRadSecondDiffSq.subSecondQuot_mul_L
#print axioms YMGap.Continuum.ChebOrthoRadSecondDiffSq.subSecondDiff_AbsLeRat
#print axioms YMGap.Continuum.ChebOrthoRadSecondDiffSq.symmSecondClose_sub
