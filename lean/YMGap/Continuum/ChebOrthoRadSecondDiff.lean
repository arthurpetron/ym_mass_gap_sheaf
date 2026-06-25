/-
# The REUSABLE √ SECOND-DIFFERENCE bounds about a cell, toward the two per-leg
# residuals `BrLegRemainder` / `RadLegRemainder` of the π-free off-diagonal
# Chebyshev-`U` orthogonality `∫_{−1}^1 U_e(x)√(1−x²)dx = 0`.

The off-diagonal core is reduced (in `ChebOrthoSecondDiff`) to TWO per-leg residuals
whose genuine √-content is the SECOND DIFFERENCE of the cell radical about the node
`x_k = (2k+1−N)/N`:

  * the SYMMETRIC second difference `s_+ + s_- − 2s_k`, and
  * the ANTISYMMETRIC first difference `s_+ − s_-`

where (writing `M = N+1`, `δ = 1/M`, `h = 2δ`)
`s_± = bdyRadical M (k±… )` are the two CELL-BOUNDARY radicals at `b_± = x_k ± δ`,
and `s_k = nodeWeight M k` is the NODE radical at `x_k`.  Geometrically
`b_k = (2k−M)/M = x_k − δ` and `b_{k+1} = (2k+2−M)/M = x_k + δ`, so
`s_- = bdyRadical M k`, `s_+ = bdyRadical M (k+1)`, and `s_k = nodeWeight M k` is the
genuine MIDPOINT radical — `s_+ + s_- − 2s_k` is a true CENTERED second difference.

## The technique (extending the codebase's radical-difference method to 2nd differences)

The codebase bounds a radical DIFFERENCE `sa − sb` (`ChebOrthoCancelDiv.bdyRadicalDiff_sharp`)
by the difference-of-squares quotient: `(sa−sb)(sa+sb) = sa²−sb²` is an EXACT rational
(the radicand difference), bounded `≤ K`; dividing by a radical-sum lower bound
`sa+sb ≥ L > 0` (`AbsLeRat.div_of_mul_ge`, reciprocal-free) gives `|sa−sb| ≤ K/L`.

This module makes that method ABSTRACT and REUSABLE for ANY two radicals:

  * **`sqrtDiff_AbsLeRat`** — THE GENERAL √-DIFFERENCE bound.  For two `CReal`s `sa, sb`
    with square collapses `sa·sa ≈ ofQ' a`, `sb·sb ≈ ofQ' b`, a two-sided radicand
    difference `|a − b| ≤ K`, a POINTWISE sum lower bound `L ≤ (sa+sb).approx n`,
    `0 < L`, and a concrete quotient `KL ≥ 0` with `KL·L ≈ K`, conclude
    `AbsLeRat (sa + (−sb)) KL` (= `|sa − sb| ≤ K/L`).  Reciprocal-free; assembles
    `radProdDiff`-style difference-of-squares (`diffOfSquares_eqv`, `sqrtFrom_sq`
    collapses) with the division primitive `AbsLeRat.div_of_mul_ge`.  `bdyRadicalDiff_sharp`
    is exactly its specialisation at two ADJACENT cell radicals.

  * The SYMMETRIC second difference is then `(s_+ − s_k) + (s_- − s_k)` and the
    ANTISYMMETRIC is `(s_+ − s_k) + (−(s_- − s_k))`; each `s_± − s_k` is a single
    √-difference handled by `sqrtDiff_AbsLeRat` (one radical a cell-boundary radical,
    the other the node radical), so BOTH second differences reduce to TWO applications
    of the general bound plus `AbsLeRat.add`.

  * **`symmSecondDiff_AbsLeRat` / `antisymmFirstDiff_AbsLeRat`** — the two reusable
    second/first-difference bounds in that assembled form, stated abstractly over the
    two per-side √-difference bounds.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on closed
`Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoCancelDiv
import YMGap.Continuum.ChebOrthoSecondDiff

namespace YMGap.Continuum.ChebOrthoRadSecondDiff

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoGradedClose
open YMGap.Continuum.ChebOrthoCancelDiv

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. A constant-difference two-sided value bound -/

/-- The DIFFERENCE-OF-RADICANDS as a constant `CReal`: `ofQ' a + (−ofQ' b)` has the
constant approximation `a + (−b)` at every index. -/
private theorem const_diff_approx (a b : Q') (n : Nat) :
    ((CReal.add (CReal.ofQ' a) (CReal.neg (CReal.ofQ' b))).approx n) ≈ (a + (-b)) :=
  Q'.eqv_refl _

/-- **The radicand-difference two-sided value bound.**  If the rational radicand
difference `a + (−b)` is two-sidedly `≤ K` (`a + (−b) ≤ K` and `−(a + (−b)) ≤ K`),
then `AbsLeRat (ofQ' a + (−ofQ' b)) K`. -/
theorem radicandDiff_AbsLeRat (a b K : Q')
    (hup : (a + (-b)) ≤ K) (hlo : (-(a + (-b))) ≤ K) :
    AbsLeRat (CReal.add (CReal.ofQ' a) (CReal.neg (CReal.ofQ' b))) K := by
  refine ⟨?_, ?_⟩
  · refine CReal.leRat_of_eventually ⟨0, fun n _ => ?_⟩
    show (a + (-b)) ≤ K
    exact hup
  · refine CReal.leRat_of_eventually ⟨0, fun n _ => ?_⟩
    show (-(a + (-b))) ≤ K
    exact hlo

/-! ## 1. THE GENERAL √-DIFFERENCE BOUND (abstract, reusable)

For ANY two radicals `sa, sb` with known square collapses and a known radical-sum
lower bound, the difference `|sa − sb|` is bounded by the reciprocal-free quotient
of the (exact rational) radicand difference by the sum lower bound. -/

/-- **THE GENERAL √-DIFFERENCE BOUND.**  Given two `CReal`s `sa, sb` with

  * square collapses `sa·sa ≈ ofQ' a`, `sb·sb ≈ ofQ' b` (`CReal.Equiv`),
  * a two-sided radicand difference `|a − b| ≤ K`,
  * a POINTWISE sum lower bound `L ≤ (sa + sb).approx n` (every index), `0 < L`,
  * a concrete quotient `KL ≥ 0` with `KL·L ≈ K`,

conclude `AbsLeRat (sa + (−sb)) KL`, i.e. `|sa − sb| ≤ K/L`, RECIPROCAL-FREE.

PROOF: the per-approximation difference-of-squares `(sa−sb)(sa+sb) ≈ sa·sa + (−sb·sb)`
(`diffOfSquares_eqv`); the squares collapse to `ofQ' a`, `ofQ' b` (the hypotheses),
so `(sa−sb)(sa+sb)` two-sidedly bounded by `|a−b| ≤ K` (`radicandDiff_AbsLeRat` +
`AbsLeRat.of_equiv` along the collapse + `AbsLeRat.congr` along diff-of-squares);
then `AbsLeRat.div_of_mul_ge` divides by the sum lower bound `L`.  No CReal reciprocal
is formed.  This is the abstract heart of `ChebOrthoCancelDiv.bdyRadicalDiff_sharp`. -/
theorem sqrtDiff_AbsLeRat {sa sb : CReal} {a b K L KL : Q'}
    (hsa : CReal.Equiv (CReal.mul sa sa) (CReal.ofQ' a))
    (hsb : CReal.Equiv (CReal.mul sb sb) (CReal.ofQ' b))
    (hKup : (a + (-b)) ≤ K) (hKlo : (-(a + (-b))) ≤ K)
    (hS : ∀ n, L ≤ (CReal.add sa sb).approx n) (hL : (0 : Q') < L)
    (hKL0 : (0 : Q') ≤ KL) (hKLid : (KL * L) ≈ K) :
    AbsLeRat (CReal.add sa (CReal.neg sb)) KL := by
  -- (1) the radicand-difference value bound
  have hRD : AbsLeRat (CReal.add (CReal.ofQ' a) (CReal.neg (CReal.ofQ' b))) K :=
    radicandDiff_AbsLeRat a b K hKup hKlo
  -- (2) transfer to the genuine squares' difference via the two collapse Equivs
  have hSqDiff : AbsLeRat
      (CReal.add (CReal.mul sa sa) (CReal.neg (CReal.mul sb sb))) K := by
    refine AbsLeRat.of_equiv ?_ hRD
    exact ChebOrthoRemainder.addNeg_Equiv_congr hsa hsb
  -- (3) transfer to the product (sa−sb)(sa+sb) via the per-approx diff-of-squares
  have hProd : AbsLeRat
      (CReal.mul (CReal.add sa (CReal.neg sb)) (CReal.add sa sb)) K := by
    refine AbsLeRat.congr ?_ hSqDiff
    intro n
    show ((sa.approx n + (-(sb.approx n))) * (sa.approx n + sb.approx n))
        ≈ (sa.approx n * sa.approx n + (-(sb.approx n * sb.approx n)))
    exact ChebOrthoCancelDiv.diffOfSquares_eqv (sa.approx n) (sb.approx n)
  -- (4) divide by the radical-sum lower bound, reciprocal-free
  exact AbsLeRat.div_of_mul_ge
    (D := CReal.add sa (CReal.neg sb)) (S := CReal.add sa sb)
    (K := K) (L := L) (KL := KL)
    hProd hS hL hKL0 hKLid

/-! ## 2. The SYMMETRIC and ANTISYMMETRIC second differences from per-side bounds

`s_+ + s_- − 2s_k = (s_+ − s_k) + (s_- − s_k)` and
`s_+ − s_- = (s_+ − s_k) + (−(s_- − s_k))`.  Given the two per-side √-difference
bounds (`|s_+ − s_k| ≤ Kp`, `|s_- − s_k| ≤ Km`) — each delivered by `sqrtDiff_AbsLeRat`
— `AbsLeRat.add` (resp. `AbsLeRat.add` with `AbsLeRat.neg`) yields the second
difference bound, EXACTLY rewriting `(s_+ + (−s_k)) + (s_- + (−s_k))` to the centered
form `s_+ + s_- + (−(2 s_k))` via a pure additive `Q'`-eqv per approximation. -/

/-- The centered-form additive identity at the approximation level:
`(P + (−Z)) + (M + (−Z)) ≈ (P + M) + (−(Z + Z))`. -/
private theorem centered_shuffle (P M Z : Q') :
    (((P + (-Z)) + (M + (-Z)))) ≈ (((P + M) + (-(Z + Z)))) := by
  calc (P + (-Z)) + (M + (-Z))
      ≈ ((P + (-Z)) + M) + (-Z) :=
        Q'.eqv_symm (Q'.add_assoc_eqv (P + (-Z)) M (-Z))
    _ ≈ ((P + M) + (-Z)) + (-Z) :=
        Q'.add_eqv_congr_right _ _ (-Z) (ChebOrthoRemainder.add_right_comm_eqv P (-Z) M)
    _ ≈ (P + M) + ((-Z) + (-Z)) := Q'.add_assoc_eqv (P + M) (-Z) (-Z)
    _ ≈ (P + M) + (-(Z + Z)) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.neg_add_eqv Z Z))

/-- The antisymmetric-form additive identity at the approximation level:
`(P + (−Z)) + (−(M + (−Z))) ≈ P + (−M)` (the two `−Z`/`Z` cancel). -/
private theorem antisymm_shuffle (P M Z : Q') :
    (((P + (-Z)) + (-(M + (-Z))))) ≈ ((P + (-M))) := by
  calc (P + (-Z)) + (-(M + (-Z)))
      ≈ (P + (-Z)) + ((-M) + (-(-Z))) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_eqv M (-Z))
    _ ≈ (P + (-Z)) + ((-M) + Z) :=
        Q'.add_eqv_congr_left _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv Z))
    _ ≈ ((P + (-Z)) + (-M)) + Z :=
        Q'.eqv_symm (Q'.add_assoc_eqv (P + (-Z)) (-M) Z)
    _ ≈ ((P + (-M)) + (-Z)) + Z :=
        Q'.add_eqv_congr_right _ _ Z (ChebOrthoRemainder.add_right_comm_eqv P (-Z) (-M))
    _ ≈ (P + (-M)) + ((-Z) + Z) := Q'.add_assoc_eqv (P + (-M)) (-Z) Z
    _ ≈ (P + (-M)) + (0 : Q') :=
        Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv Z)
    _ ≈ (P + (-M)) := QPoly.q_add_zero_eqv _

/-- **THE SYMMETRIC √ SECOND-DIFFERENCE BOUND (assembled).**  Given the two per-side
√-difference bounds `|s_+ − s_k| ≤ Kp` and `|s_- − s_k| ≤ Km`, the SYMMETRIC second
difference about the node is bounded:

    `AbsLeRat (s_+ + s_- + (−(s_k + s_k))) (Kp + Km)`,

i.e. `|s_+ + s_- − 2 s_k| ≤ Kp + Km`.  PROOF: `AbsLeRat.add` of the two per-side
bounds gives `AbsLeRat ((s_+ + (−s_k)) + (s_- + (−s_k))) (Kp + Km)`; the per-approx
`centered_shuffle` rewrites the body to the centered form `s_+ + s_- + (−(s_k + s_k))`
(`AbsLeRat.congr`). -/
theorem symmSecondDiff_AbsLeRat {sP sM sK : CReal} {Kp Km : Q'}
    (hP : AbsLeRat (CReal.add sP (CReal.neg sK)) Kp)
    (hM : AbsLeRat (CReal.add sM (CReal.neg sK)) Km) :
    AbsLeRat
      (CReal.add (CReal.add sP sM) (CReal.neg (CReal.add sK sK)))
      (Kp + Km) := by
  have hadd := AbsLeRat.add hP hM
  refine AbsLeRat.congr ?_ hadd
  intro n
  show ((sP.approx n + sM.approx n) + (-(sK.approx n + sK.approx n)))
      ≈ ((sP.approx n + (-(sK.approx n))) + (sM.approx n + (-(sK.approx n))))
  exact Q'.eqv_symm (centered_shuffle (sP.approx n) (sM.approx n) (sK.approx n))

/-- **THE ANTISYMMETRIC √ FIRST-DIFFERENCE BOUND (assembled).**  Given the two
per-side √-difference bounds `|s_+ − s_k| ≤ Kp` and `|s_- − s_k| ≤ Km`, the
difference of the two cell-boundary radicals is bounded:

    `AbsLeRat (s_+ + (−s_-)) (Kp + Km)`,

i.e. `|s_+ − s_-| ≤ Kp + Km`.  PROOF: `AbsLeRat.add` of `hP` and the negated `hM`
gives `AbsLeRat ((s_+ + (−s_k)) + (−(s_- + (−s_k)))) (Kp + Km)`; the per-approx
`antisymm_shuffle` cancels the two `s_k` terms to `s_+ + (−s_-)` (`AbsLeRat.congr`). -/
theorem antisymmFirstDiff_AbsLeRat {sP sM sK : CReal} {Kp Km : Q'}
    (hP : AbsLeRat (CReal.add sP (CReal.neg sK)) Kp)
    (hM : AbsLeRat (CReal.add sM (CReal.neg sK)) Km) :
    AbsLeRat (CReal.add sP (CReal.neg sM)) (Kp + Km) := by
  have hMneg : AbsLeRat (CReal.neg (CReal.add sM (CReal.neg sK))) Km := AbsLeRat.neg hM
  have hadd := AbsLeRat.add hP hMneg
  refine AbsLeRat.congr ?_ hadd
  intro n
  show (sP.approx n + (-(sM.approx n)))
      ≈ ((sP.approx n + (-(sK.approx n))) + (-(sM.approx n + (-(sK.approx n)))))
  exact Q'.eqv_symm (antisymm_shuffle (sP.approx n) (sM.approx n) (sK.approx n))

/-! ## 3. CONCRETE building blocks: node-vs-boundary square collapses + radicand diff

The two per-side √-differences feeding the second differences are `s_+ − s_k` and
`s_- − s_k`, with `s_± = bdyRadical M (k±)` (cell-boundary radicals at `b_± = x_k ± δ`)
and `s_k = nodeWeight M k` (the node radical at `x_k`).  To instantiate
`sqrtDiff_AbsLeRat` we supply: the two square collapses, and the EXACT rational
radicand difference. -/

open YMGap.Continuum.ChebOrthoMidpoint
open YMGap.Continuum.SemicircleIntegral

/-- **The cell-boundary radical square collapse.**  `s_b · s_b ≈ ofQ'(1 − b_k²)` for
an interior cell `0 < k`, `k < M` (the `sqrtFrom` square collapse after the interior
unfolding `bdyRadical_interior`). -/
theorem bdyRadical_sq_collapse (M : Nat) (hM : 0 < M) (k : Nat) (hk0 : 0 < k) (hkn : k < M) :
    CReal.Equiv (CReal.mul (bdyRadical M hM k) (bdyRadical M hM k))
      (CReal.ofQ' (bdyOneMinusSq M k hM hk0 hkn)) := by
  rw [ChebOrthoRemainder.bdyRadical_interior M hM k hk0 hkn]
  exact CReal.sqrtFrom_sq_equiv (bdyOneMinusSq M k hM hk0 hkn)
    (SemicircleIntegral.nodeLB M hM) (bdyOneMinusSq_pos hM hk0 hkn)
    (SemicircleIntegral.nodeLB_pos hM) (bdyLB_sq_le hM hk0 hkn)

/-- **The EXACT node-vs-right-boundary radicand difference (Int numerators).**
`bdyNum M (k+1) − omsNum M k = −(2·(2k+1−M) + 1)`.  Both radicands share the
denominator `M²`; the numerator difference is `(2k+1−M)² − (2k+2−M)²` = `A² − (A+1)²
= −(2A+1)`, `A = 2k+1−M` (the centered first step `b_{k+1}² − x_k² = δ(2x_k+δ)`
cleared of `M²`). -/
theorem bdyNum_omsNum_diff_right (M k : Nat) :
    bdyNum M (k + 1) - omsNum M k = -(2 * (2 * (k : Int) + 1 - (M : Int)) + 1) := by
  show ((M : Int) * (M : Int)
        - (2 * ((k + 1 : Nat) : Int) - (M : Int)) * (2 * ((k + 1 : Nat) : Int) - (M : Int)))
      - ((M : Int) * (M : Int)
        - (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)))
    = -(2 * (2 * (k : Int) + 1 - (M : Int)) + 1)
  have hcast : (2 * ((k + 1 : Nat) : Int) - (M : Int))
      = ((2 * (k : Int) + 1 - (M : Int)) + 1) := by push_cast; omega
  rw [hcast]
  -- (M² − (A+1)²) − (M² − A²) = A² − (A+1)² = −(2A+1), A = 2k+1−M.
  generalize hA : (2 * (k : Int) + 1 - (M : Int)) = A
  have hexp : (A + 1) * (A + 1) = A * A + 2 * A + 1 := by
    have h1 : (A + 1) * (A + 1) = A * (A + 1) + 1 * (A + 1) := Int.add_mul A 1 (A + 1)
    have h2 : A * (A + 1) = A * A + A * 1 := Int.mul_add A A 1
    omega
  omega

/-- **The EXACT node-vs-left-boundary radicand difference (Int numerators).**
`bdyNum M k − omsNum M k = 2·(2k+1−M) − 1`.  Numerator difference
`A² − (A−1)² = 2A−1`, `A = 2k+1−M` (the centered first step `x_k² − b_k² = δ(2x_k−δ)`,
so `(1−b_k²) − (1−x_k²) = +(2A−1)/M²`). -/
theorem bdyNum_omsNum_diff_left (M k : Nat) :
    bdyNum M k - omsNum M k = 2 * (2 * (k : Int) + 1 - (M : Int)) - 1 := by
  show ((M : Int) * (M : Int)
        - (2 * (k : Int) - (M : Int)) * (2 * (k : Int) - (M : Int)))
      - ((M : Int) * (M : Int)
        - (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)))
    = 2 * (2 * (k : Int) + 1 - (M : Int)) - 1
  have hcast : (2 * (k : Int) - (M : Int))
      = ((2 * (k : Int) + 1 - (M : Int)) - 1) := by omega
  rw [hcast]
  generalize hA : (2 * (k : Int) + 1 - (M : Int)) = A
  have hexp : (A - 1) * (A - 1) = A * A - 2 * A + 1 := by
    have h1 : (A - 1) * (A - 1) = A * (A - 1) - 1 * (A - 1) := Int.sub_mul A 1 (A - 1)
    have h2 : A * (A - 1) = A * A - A * 1 := Int.mul_sub A A 1
    omega
  omega

/-! ## 4. The concrete per-side √-difference, reduced to a NAMED quotient residual

With the two square collapses and the exact radicand differences in hand, the per-side
√-difference `|s_± − s_k|` is delivered by `sqrtDiff_AbsLeRat` once supplied with:
(i) a two-sided radicand-difference bound `|(1−b²) − (1−x_k²)| ≤ K` (immediate from the
exact `Q'` numerator differences above), (ii) a pointwise sum lower bound
`L ≤ (s_± + s_k).approx n` (a `bdyRadical_geRat`/`nodeWeight_approx_ge` mix), and
(iii) a concrete quotient `KL` with `KL·L ≈ K`, `KL ≥ 0`.  Items (i)–(ii) are
PROVED-shaped (the exact differences here + the existing pointwise lower bounds); the
ONE irreducible numeric atom is the explicit reciprocal-free quotient and its defining
product identity — exactly the `sharpBound`/`sharpBound_mul_recipWitness` pattern of
`ChebOrthoCancelDiv`, specialised to the node-vs-boundary denominator.  We name it as a
STRICTLY SMALLER per-side residual with a PROVED reduction to `sqrtDiff_AbsLeRat`. -/

/-- **NAMED-open (per-side quotient data).**  The reciprocal-free quotient certificate
for a single node-vs-boundary √-difference: a concrete `Q'` value `KL ≥ 0` with the
product identity `KL · L ≈ K`, where `K` two-sidedly bounds the (exact rational)
radicand difference and `L` lower-bounds the radical sum.  Bundled as Type-level data
(MLTT-valid: the witness `KL` is data, the identities are its fields). -/
structure SqrtDiffQuotient (a b K L : Q') : Type where
  /-- the explicit reciprocal-free quotient value `K/L`. -/
  KL : Q'
  /-- `KL ≥ 0`. -/
  KL_nonneg : (0 : Q') ≤ KL
  /-- the radicand-difference two-sided bound (upper). -/
  K_up : (a + (-b)) ≤ K
  /-- the radicand-difference two-sided bound (lower). -/
  K_lo : (-(a + (-b))) ≤ K
  /-- the defining product identity `KL · L ≈ K`. -/
  KL_id : (KL * L) ≈ K

/-- **THE PER-SIDE REDUCTION.**  Given the two square collapses, a pointwise radical-sum
lower bound `L ≤ (sa+sb).approx n` (`0 < L`), and a `SqrtDiffQuotient` certificate,
the per-side √-difference is bounded `|sa − sb| ≤ KL`.  PROVED reduction to the general
`sqrtDiff_AbsLeRat` (it unbundles the certificate's fields).  This isolates the SINGLE
remaining numeric atom (the explicit quotient `KL` with `KL·L ≈ K`) as Type-level data. -/
theorem perSideSqrtDiff_of_quotient {sa sb : CReal} {a b L : Q'} {K : Q'}
    (hsa : CReal.Equiv (CReal.mul sa sa) (CReal.ofQ' a))
    (hsb : CReal.Equiv (CReal.mul sb sb) (CReal.ofQ' b))
    (hS : ∀ n, L ≤ (CReal.add sa sb).approx n) (hL : (0 : Q') < L)
    (q : SqrtDiffQuotient a b K L) :
    AbsLeRat (CReal.add sa (CReal.neg sb)) q.KL :=
  sqrtDiff_AbsLeRat hsa hsb q.K_up q.K_lo hS hL q.KL_nonneg q.KL_id

end YMGap.Continuum.ChebOrthoRadSecondDiff

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `radicandDiff_AbsLeRat` — the constant radicand-difference two-sided value bound
    `|a − b| ≤ K → AbsLeRat (ofQ' a + (−ofQ' b)) K`.
  * **`sqrtDiff_AbsLeRat`** — THE GENERAL reciprocal-free √-DIFFERENCE bound: for two
    radicals `sa, sb` with square collapses `sa² ≈ ofQ' a`, `sb² ≈ ofQ' b`, a
    two-sided radicand difference `|a−b| ≤ K`, a pointwise sum lower bound
    `L ≤ (sa+sb).approx n` (`0 < L`), and a concrete quotient `KL ≥ 0` with `KL·L ≈ K`,
    conclude `AbsLeRat (sa + (−sb)) KL` (= `|sa − sb| ≤ K/L`).  The abstract heart of
    `ChebOrthoCancelDiv.bdyRadicalDiff_sharp`, now reusable for ANY two radicals
    (e.g. a cell-boundary radical vs the node radical).
  * **`symmSecondDiff_AbsLeRat`** — the SYMMETRIC √ second-difference bound
    `|s_+ + s_- − 2 s_k| ≤ Kp + Km` assembled from the two per-side √-difference
    bounds (`|s_+ − s_k| ≤ Kp`, `|s_- − s_k| ≤ Km`) via `AbsLeRat.add` and the
    centered additive shuffle.
  * **`antisymmFirstDiff_AbsLeRat`** — the ANTISYMMETRIC √ first-difference bound
    `|s_+ − s_-| ≤ Kp + Km` assembled the same way (with one side negated).

**Path of use.**  Instantiate `sqrtDiff_AbsLeRat` twice — once with
`sa = s_+ = bdyRadical M (k+1)`, `sb = s_k = nodeWeight M k` (square collapses
`ChebOrthoRemainder.radSq` / `ChebOrthoLeadingModel.node_sq_collapse`; radicand
difference `1 − b_{k+1}² − (1 − x_k²)`, an EXACT rational; sum lower bound from a
`bdyRadical_geRat` / `nodeWeight_approx_ge` mix), once with the left side — to obtain
`Kp`, `Km`; then `symmSecondDiff_AbsLeRat` / `antisymmFirstDiff_AbsLeRat` give the two
second-difference bounds that power `BrLegRemainder` / `RadLegRemainder` after the
bracket-factor multiplication and the exponent balance to `½·gradedRate`.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoRadSecondDiff.radicandDiff_AbsLeRat
#print axioms YMGap.Continuum.ChebOrthoRadSecondDiff.sqrtDiff_AbsLeRat
#print axioms YMGap.Continuum.ChebOrthoRadSecondDiff.symmSecondDiff_AbsLeRat
#print axioms YMGap.Continuum.ChebOrthoRadSecondDiff.antisymmFirstDiff_AbsLeRat
#print axioms YMGap.Continuum.ChebOrthoRadSecondDiff.bdyRadical_sq_collapse
#print axioms YMGap.Continuum.ChebOrthoRadSecondDiff.bdyNum_omsNum_diff_right
#print axioms YMGap.Continuum.ChebOrthoRadSecondDiff.bdyNum_omsNum_diff_left
#print axioms YMGap.Continuum.ChebOrthoRadSecondDiff.perSideSqrtDiff_of_quotient
