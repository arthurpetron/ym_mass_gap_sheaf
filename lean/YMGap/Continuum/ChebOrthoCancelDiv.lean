/-
# The CANCELLATION / DIVISION primitive for the `AbsLeRat` two-sided value calculus,
# and the SHARP reciprocal-free radical-difference bound
# `|s_+ − s_-| ≤ 4|2k+1−M|δ / recipWitness` for interior cells — the key
# ingredient for the off-diagonal `∫ U_e √(1−x²) dx = 0` final assembly.

The companion modules reduce the even-order off-diagonal orthogonality to the SINGLE
interior per-cell two-sided estimate; the radical leg of that estimate needs the
SHARP reciprocal-free difference `|s_+ − s_-|` of the two adjacent cell radicals,
obtained by dividing the exact squared difference `s_+² − s_-² = −4x_kδ` by the
constructive reciprocal lower bound `s_+ + s_- ≥ recipWitness` — with NO CReal
reciprocal.

The limit-level cancellation that makes this possible is the GENERAL primitive
`AbsLeRat.div_of_mul_ge`: from `|D·S| ≤ K`, a pointwise lower bound `S ≥ L > 0`, and
a concrete rational quotient `KL` with `KL·L ≈ K` and `KL ≥ 0`, conclude `|D| ≤ KL`.
Its two `leRat` directions use a constructive sign split on `D` (the negative side is
free; the positive side multiplies the lower bound `L ≤ S` and cancels `L > 0`).

## What is PROVED here (axiom-clean, GENUINE new content)

  * `Q'.le_of_mul_le_mul_right_pos` — the rational cancellation `a·c ≤ b·c → 0 < c →
    a ≤ b` (cross-multiplication + `Int.le_of_mul_le_mul_right`).

  * **`AbsLeRat.div_of_mul_ge`** — the GENERAL cancellation/division primitive for the
    `AbsLeRat` two-sided value calculus: `|D·S| ≤ K`, `(∀ n, L ≤ S.approx n)`,
    `0 < L`, `KL·L ≈ K`, `0 ≤ KL` ⟹ `|D| ≤ KL`.  Reciprocal-free; the only "division"
    is supplying the concrete quotient `KL` and proving `KL·L ≈ K`.

  * `interiorRadicalSum_ptwise` — the POINTWISE reciprocal lower bound
    `recipWitness M j ≤ (s_+ + s_-).approx n` at every Heron index (the exact form the
    division primitive consumes, derived from `ChebOrthoInterior.bdyRadical_geRat` and
    `bdyRadical_approx_nonneg`).

  * `radProdDiff_AbsLeRat` — the two-sided value bound on the squared difference
    `AbsLeRat (D·S) (4|2k+1−M|/M²)`, `D = s_+ − s_-`, `S = s_+ + s_-`, via the EXACT
    `s_+² − s_-² = −4x_kδ` (`ChebOrthoRemainder.radSq_diff_equiv` +
    `ChebOrthoRemainder.bdyOneMinusSq_diff`) and the per-approximation ring identity
    `(a−b)(a+b) = a²−b²`.

  * **`bdyRadicalDiff_sharp`** — THE SHARP reciprocal-free radical-difference bound

        `AbsLeRat (s_+ + (−s_-)) (sharpBound M k)`,
        `sharpBound M k = mkPos (4·|2k+1−M|·M) (M²·⌊√(4(j−1)j)⌋)`  (= 4|x_k|δ / recipWitness),

    for an interior cell (`0 < k`, `k+1 < M`, `jdist M k ≥ 2`), obtained by applying
    the division primitive to `radProdDiff_AbsLeRat` and `interiorRadicalSum_ptwise`.
    This is the residual #1 named in the off-diagonal assembly, now PROVED.

## What is NAMED-open (precisely)

  * `ChebOrthoGradedClose.InteriorGradedRemainder e he` — the full interior per-cell
    two-sided estimate against `gradedRate = C(e)/(⌊√M⌋·jdist²)`.  With BOTH the
    √-Hölder radical difference and now the SHARP reciprocal-free radical difference
    PROVED, the residual is the NUMERIC second-order assembly: combine the
    product-difference split + the leading cancellation with the smooth-bracket-leg
    Lipschitz scale `Le e` (`R_poly`) and this sharp radical-leg bound (`R_rad`), then
    balance the exponents `4|x_k|δ/recipWitness ~ δ^{3/2}/j^{3/2} ≤ 1/(⌊√M⌋·j²)` to
    `gradedRate`.  Recorded precisely, NOT faked.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on closed
`Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoInterior
import YMGap.Continuum.ChebOrthoRemainder
import YMGap.Continuum.ChebOrthoGradedClose
import YMGap.Continuum.ChebOrthoMidpoint

namespace YMGap.Continuum.ChebOrthoCancelDiv

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoMidpoint
open YMGap.Continuum.ChebOrthoGraded
open YMGap.Continuum.ChebOrthoGradedClose
open YMGap.Continuum.ChebOrthoInterior

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Rational cancellation by a positive factor -/

/-- `Int` reorder of a 4-fold product `(w·x)·(y·z) = (w·y)·(x·z)`. -/
private theorem int_reorder4 (w x y z : Int) : (w * x) * (y * z) = (w * y) * (x * z) := by
  simp only [Int.mul_left_comm, Int.mul_comm]

/-- **Rational cancellation by a positive factor.**  `a·c ≤ b·c` and `0 < c` give
`a ≤ b`.  Cross-multiplying the `Q'`-`≤` of the two products and cancelling the
common positive factor `c.num·c.den` via `Int.le_of_mul_le_mul_right`. -/
theorem Q'.le_of_mul_le_mul_right_pos (a b c : Q') (hc : (0 : Q') < c)
    (h : a * c ≤ b * c) : a ≤ b := by
  -- a*c ≤ b*c :  (a.num*c.num)*(b.den*c.den) ≤ (b.num*c.num)*(a.den*c.den)
  have h' : (a.num * c.num) * (((b.den * c.den : Nat)) : Int)
      ≤ (b.num * c.num) * (((a.den * c.den : Nat)) : Int) := h
  -- 0 < c.num (from 0 < c) and 0 < c.den
  have hcnum : (0 : Int) < c.num := Q'.num_pos_of_pos hc
  have hcden : (0 : Int) < (c.den : Int) := by exact_mod_cast Q'.den_pos c
  have hccpos : (0 : Int) < c.num * (c.den : Int) := Int.mul_pos hcnum hcden
  -- cast the Nat products and rearrange to expose the common factor (c.num*c.den)
  have hcast_b : (((b.den * c.den : Nat)) : Int) = (b.den : Int) * (c.den : Int) := by
    push_cast; rfl
  have hcast_a : (((a.den * c.den : Nat)) : Int) = (a.den : Int) * (c.den : Int) := by
    push_cast; rfl
  rw [hcast_b, hcast_a] at h'
  -- (a.num*c.num)*(b.den*c.den) = (a.num*b.den)*(c.num*c.den)
  have eL : (a.num * c.num) * ((b.den : Int) * (c.den : Int))
      = (a.num * (b.den : Int)) * (c.num * (c.den : Int)) :=
    int_reorder4 a.num c.num (b.den : Int) (c.den : Int)
  have eR : (b.num * c.num) * ((a.den : Int) * (c.den : Int))
      = (b.num * (a.den : Int)) * (c.num * (c.den : Int)) :=
    int_reorder4 b.num c.num (a.den : Int) (c.den : Int)
  rw [eL, eR] at h'
  -- cancel the positive common factor
  show a.num * (b.den : Int) ≤ b.num * (a.den : Int)
  exact Int.le_of_mul_le_mul_right h' hccpos

/-! ## 1. The general cancellation / division primitive -/

/-- **THE CANCELLATION / DIVISION PRIMITIVE** for the `AbsLeRat` two-sided value
calculus.  Given `|D·S| ≤ K`, a POINTWISE lower bound `L ≤ S.approx n` (every Heron
index), `0 < L`, and a concrete rational quotient `KL ≥ 0` with `KL·L ≈ K`, conclude
`|D| ≤ KL`.

This is the reciprocal-free `D·S ≈ ofQ' c`, `S ≥ L > 0`, `|c| ≤ K ⟹ |D| ≤ K/L`
lemma whose two `leRat` directions need a constructive sign split on `D`.  PROOF (per
direction, per approximation `n`): sign-case on `D.approx n` (resp. `−D.approx n`).
The non-positive case is free (`D_n ≤ 0 ≤ KL`).  The positive case multiplies the
pointwise lower bound `L ≤ S_n` by `D_n ≥ 0` to get `D_n·L ≤ D_n·S_n ≤ K + ε·L`,
rewrites `K + ε·L ≈ (KL + ε)·L`, and cancels `L > 0` (`Q'.le_of_mul_le_mul_right_pos`)
to land at `D_n ≤ KL + ε`.  No CReal reciprocal is ever formed. -/
theorem AbsLeRat.div_of_mul_ge {D S : CReal} {K L KL : Q'}
    (hDS : AbsLeRat (CReal.mul D S) K)
    (hS : ∀ n, L ≤ S.approx n) (hL : (0 : Q') < L)
    (hKL0 : (0 : Q') ≤ KL) (hKLid : (KL * L) ≈ K) :
    AbsLeRat D KL := by
  -- the two AbsLeRat halves of hDS
  obtain ⟨hUp, hLo⟩ := hDS
  -- a reusable per-direction core:  for a CReal `E` with `E_n·S_n ≤ K + ε` eventually
  -- and `E_n ≤ 0 ∨ 0 < E_n`, show `leRat E KL`.
  have core : ∀ E : CReal, (CReal.leRat (CReal.mul E S) K) → CReal.leRat E KL := by
    intro E hE
    intro ε hε
    -- tolerance on the product side:  ε·L > 0
    have hεL : (0 : Q') < ε * L := by
      have hεn : (0 : Int) < ε.num := Q'.num_pos_of_pos hε
      have hLn : (0 : Int) < L.num := Q'.num_pos_of_pos hL
      show (0 : Q').num * ((ε * L).den : Int) < (ε * L).num * ((0 : Q').den : Int)
      show (0 : Q').num * ((ε * L).den : Int) < (ε.num * L.num) * ((0 : Q').den : Int)
      have h0n : (0 : Q').num = 0 := rfl
      have hd1 : ((0 : Q').den : Int) = 1 := rfl
      rw [h0n, hd1, Int.zero_mul, Int.mul_one]
      exact Int.mul_pos hεn hLn
    obtain ⟨N, hN⟩ := hE (ε * L) hεL
    refine ⟨N, fun n hn => ?_⟩
    -- hN n hn : (mul E S).approx n ≤ K + ε*L,  i.e.  E_n·S_n ≤ K + ε*L
    have hprod : E.approx n * S.approx n ≤ K + ε * L := hN n hn
    -- sign-case on E_n
    by_cases hpos : (0 : Q') ≤ E.approx n
    · -- E_n ≥ 0 :  E_n·L ≤ E_n·S_n ≤ K + ε*L ≈ (KL+ε)*L, cancel L > 0
      have hEL : E.approx n * L ≤ E.approx n * S.approx n :=
        Q'.mul_le_mul_of_nonneg_left L (S.approx n) (E.approx n) (hS n) hpos
      have hELK : E.approx n * L ≤ K + ε * L := Q'.le_trans' _ _ _ hEL hprod
      -- (KL+ε)*L ≈ KL*L + ε*L ≈ K + ε*L
      have hexp : ((KL + ε) * L) ≈ (K + ε * L) := by
        refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv KL ε L) ?_
        exact Q'.add_eqv_congr_right _ _ _ hKLid
      have hELKL : E.approx n * L ≤ (KL + ε) * L :=
        Q'.le_trans' _ _ _ hELK (Q'.ge_of_eqv hexp)
      exact Q'.le_of_mul_le_mul_right_pos (E.approx n) (KL + ε) L hL hELKL
    · -- E_n < 0 :  E_n ≤ 0 ≤ KL ≤ KL + ε
      have hEn0 : E.approx n ≤ (0 : Q') := Q'.nonpos_of_not_nonneg hpos
      have hKLε : (0 : Q') ≤ KL + ε :=
        Q'.zero_le_add KL ε hKL0 (Q'.le_of_lt hε)
      exact Q'.le_trans' _ _ _ hEn0 hKLε
  -- upper side:  leRat D KL  via core on D
  refine ⟨core D hUp, ?_⟩
  -- lower side:  leRat (neg D) KL  via core on (neg D), using (neg D)·S = neg (D·S)
  -- leRat ((neg D)·S) K  from hLo : leRat (neg (D·S)) K  (pointwise eqv)
  have hcong : ∀ n, ((CReal.mul (CReal.neg D) S).approx n)
      ≈ ((CReal.neg (CReal.mul D S)).approx n) := by
    intro n
    show ((-(D.approx n)) * S.approx n) ≈ (-(D.approx n * S.approx n))
    exact Q'.neg_mul_eqv (D.approx n) (S.approx n)
  have hNegProd : CReal.leRat (CReal.mul (CReal.neg D) S) K :=
    CReal.leRat_congr hcong hLo
  exact core (CReal.neg D) hNegProd

/-- `AbsLeRat` transfers across a `CReal.Equiv` (same limit ⇒ same two-sided bound).
The upper side is `CReal.leRat_of_equiv`; the lower side uses the negation `Equiv`. -/
theorem AbsLeRat.of_equiv {x y : CReal} {b : Q'} (h : CReal.Equiv x y) (hy : AbsLeRat y b) :
    AbsLeRat x b := by
  refine ⟨CReal.leRat_of_equiv h hy.1, ?_⟩
  -- neg x Equiv neg y, then leRat_of_equiv on the lower side
  have hneg : CReal.Equiv (CReal.neg x) (CReal.neg y) := by
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨h1, h2⟩ := hN n hn
    -- (neg x).approx n = −x_n ;  −x_n ≤ −y_n + ε  from  y_n ≤ x_n + ε
    show (-(x.approx n)) ≤ (-(y.approx n)) + ε ∧ (-(y.approx n)) ≤ (-(x.approx n)) + ε
    exact ⟨Q'.neg_le_neg_add h2, Q'.neg_le_neg_add h1⟩
  exact CReal.leRat_of_equiv hneg hy.2

/-! ## 2. The pointwise reciprocal lower bound on the sum of the two cell radicals -/

/-- **POINTWISE reciprocal lower bound** on the sum of the two adjacent interior cell
radicals.  For an interior cell `0 < k < M` whose distance `j := jdist M k` satisfies
`2 ≤ j`, at EVERY Heron index `n`:

    `recipWitness M j ≤ (s_+ + s_-).approx n`,    `s_± = √(1 − b_{k±}²)`.

This is the exact pointwise form `(∀ n, L ≤ S.approx n)` that `div_of_mul_ge`
consumes, derived from the constructive lower bound `bdyRadical_geRat` on `s_-`
(`recipWitness² ≤ 1 − b_k²` via `recipWitness_sq_le`) and `bdyRadical_approx_nonneg`
on `s_+`. -/
theorem interiorRadicalSum_ptwise (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hj : 2 ≤ jdist M k) (n : Nat) :
    recipWitness M (jdist M k) hM
      ≤ (CReal.add (bdyRadical M hM (k + 1)) (bdyRadical M hM k)).approx n := by
  show recipWitness M (jdist M k) hM
      ≤ (bdyRadical M hM (k + 1)).approx n + (bdyRadical M hM k).approx n
  -- s_-.approx n ≥ recipWitness  (bdyRadical_geRat with L = recipWitness)
  have hLpos := ChebOrthoInterior.recipWitness_pos M (jdist M k) hM hj
  have hLsq := ChebOrthoInterior.recipWitness_sq_le M hM k hk0 hkn hj
  have hsm : recipWitness M (jdist M k) hM ≤ (bdyRadical M hM k).approx n := by
    rw [ChebOrthoRemainder.bdyRadical_interior M hM k hk0 hkn]
    show recipWitness M (jdist M k) hM
        ≤ (CReal.sqrtFrom (bdyOneMinusSq M k hM hk0 hkn) (SemicircleIntegral.nodeLB M hM)
            (bdyOneMinusSq_pos hM hk0 hkn) (SemicircleIntegral.nodeLB_pos hM)
            (bdyLB_sq_le hM hk0 hkn)).approx n
    rw [CReal.sqrtFrom_approx]
    exact CReal.heronSeq_lb (bdyOneMinusSq M k hM hk0 hkn) (recipWitness M (jdist M k) hM)
      (bdyOneMinusSq_pos hM hk0 hkn) hLpos hLsq n
  -- s_+.approx n ≥ 0
  have hsp : (0 : Q') ≤ (bdyRadical M hM (k + 1)).approx n :=
    ChebOrthoInterior.bdyRadical_approx_nonneg M hM (k + 1) n
  -- recipWitness = 0 + recipWitness ≤ s_+ + s_-
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_zero_add_eqv _)) ?_
  exact Q'.add_le_add hsp hsm

/-! ## 3. The squared-difference value bound `|D·S| ≤ 4|2k+1−M|/M²` -/

/-- The pure-`Q'` difference-of-squares identity `(a + (−b))·(a + b) ≈ a·a + (−(b·b))`.
A chain of the distributive `eqv` laws (`add_mul_eqv`, `mul_add_eqv`, `mul_neg`,
`neg_mul`) and an abelian regroup cancelling the cross terms `a·b` and `−(a·b)`. -/
theorem diffOfSquares_eqv (a b : Q') :
    ((a + (-b)) * (a + b)) ≈ (a * a + (-(b * b))) := by
  -- (a+(−b))·(a+b) ≈ a·(a+b) + (−b)·(a+b)
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv a (-b) (a + b)) ?_
  -- ≈ (a·a + a·b) + ((−b)·a + (−b)·b)
  have e1 : (a * (a + b)) ≈ (a * a + a * b) := Q'.mul_add_eqv a a b
  have e2 : ((-b) * (a + b)) ≈ ((-b) * a + (-b) * b) := Q'.mul_add_eqv (-b) a b
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ e1)
      (Q'.add_eqv_congr_left _ _ _ e2)) ?_
  -- ((a·a + a·b) + ((−b)·a + (−b)·b))
  -- rewrite (−b)·a ≈ −(a·b)  and  (−b)·b ≈ −(b·b)
  have e3 : ((-b) * a) ≈ (-(a * b)) :=
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv b a)
      (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv b a))
  have e4 : ((-b) * b) ≈ (-(b * b)) := Q'.neg_mul_eqv b b
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ e3)
        (Q'.add_eqv_congr_left _ _ _ e4))) ?_
  -- now: (a·a + a·b) + ((−(a·b)) + (−(b·b)))  ≈  a·a + (−(b·b))
  -- regroup: ((a·a + a·b) + (−(a·b))) + (−(b·b))  then cancel a·b + (−(a·b))
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (a * a + a * b) (-(a * b)) (-(b * b)))) ?_
  refine Q'.add_eqv_congr_right _ _ _ ?_
  -- (a·a + a·b) + (−(a·b)) ≈ a·a
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (a * a) (a * b) (-(a * b))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv (a * b))) ?_
  exact QPoly.q_add_zero_eqv (a * a)

/-- The signed radicand difference numerator `−4·(2k+1−M)` and the absolute bound
`K := mkPos (4·|2k+1−M|) (M²)`. -/
def xkAbs (M k : Nat) : Nat := (2 * (k : Int) + 1 - (M : Int)).natAbs

/-- The two-sided value bound `K = 4·|2k+1−M|/M²` on the radicand difference. -/
def radDiffBound (M k : Nat) (hM : 0 < M) : Q' :=
  Q'.mkPos (4 * (xkAbs M k : Int)) (M * M) (Nat.mul_pos hM hM)

/-- **The squared-difference value bound.**  For an interior pair `0 < k`, `k+1 < M`,
the product `D·S = (s_+ − s_-)(s_+ + s_-) = s_+² − s_-²` is two-sidedly
`≤ 4·|2k+1−M|/M²`:

    `AbsLeRat ((s_+ + (−s_-)) · (s_+ + s_-)) (radDiffBound M k)`.

PROOF: `radSq_diff_equiv` collapses `s_+² + (−s_-²)` to `ofQ'(1−b_{k+1}²) +
(−ofQ'(1−b_k²))`, whose constant limit is the rational
`(1−b_{k+1}²) − (1−b_k²) ≈ −4(2k+1−M)/M²` (`bdyOneMinusSq_diff`), two-sidedly `≤ K`;
this transfers to `D·S` through the per-approximation difference-of-squares identity
`diffOfSquares_eqv` (`AbsLeRat.congr`) and the squares' `Equiv` (`AbsLeRat.of_equiv`). -/
theorem radProdDiff_AbsLeRat (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    AbsLeRat
      (CReal.mul (CReal.add (bdyRadical M hM (k + 1)) (CReal.neg (bdyRadical M hM k)))
        (CReal.add (bdyRadical M hM (k + 1)) (bdyRadical M hM k)))
      (radDiffBound M k hM) := by
  -- abbreviations for the two radicands (plain `let`, definitionally transparent)
  let radp := bdyOneMinusSq M (k + 1) hM (Nat.succ_pos k) hk1n
  let radm := bdyOneMinusSq M k hM hk0 hkn
  -- the constant value of R := ofQ' radp + (−ofQ' radm) is q0 = radp + (−radm).
  let q0 : Q' := radp + (-radm)
  -- (1) AbsLeRat R (radDiffBound) where R = add (ofQ' radp) (neg (ofQ' radm))
  have hR : AbsLeRat (CReal.add (CReal.ofQ' radp) (CReal.neg (CReal.ofQ' radm)))
      (radDiffBound M k hM) := by
    -- R.approx n = radp + (−radm) = q0  (constant), and |q0| ≤ K.
    have hq0eqv : q0 ≈ (Q'.mkPos (-(4 * (2 * (k : Int) + 1 - (M : Int))))
            (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM)) :=
      ChebOrthoRemainder.bdyOneMinusSq_diff M k hM hk0 hkn hk1n
    -- |q0| ≤ K :  q0 ≈ mkPos(−4(2k+1−M)) (M²),  K = mkPos(4|2k+1−M|) (M²)
    -- numerator comparison after the eqv.
    have hMM : (SemicircleIntegral.omsDen M) = M * M := rfl
    -- q0 ≤ K
    have hq0_le : q0 ≤ radDiffBound M k hM := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hq0eqv) ?_
      -- mkPos(−4(2k+1−M)) (M²) ≤ mkPos(4|2k+1−M|) (M²) : numerator −4(2k+1−M) ≤ 4|2k+1−M|
      show (Q'.mkPos (-(4 * (2 * (k : Int) + 1 - (M : Int))))
              (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM)).num
            * ((radDiffBound M k hM).den : Int)
          ≤ (radDiffBound M k hM).num
            * ((Q'.mkPos (-(4 * (2 * (k : Int) + 1 - (M : Int))))
                  (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM)).den : Int)
      rw [Q'.mkPos_num]
      show (-(4 * (2 * (k : Int) + 1 - (M : Int)))) * ((radDiffBound M k hM).den : Int)
          ≤ (radDiffBound M k hM).num
            * ((Q'.mkPos (-(4 * (2 * (k : Int) + 1 - (M : Int))))
                  (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM)).den : Int)
      rw [Q'.mkPos_den]
      show (-(4 * (2 * (k : Int) + 1 - (M : Int)))) * ((radDiffBound M k hM).den : Int)
          ≤ (radDiffBound M k hM).num * ((SemicircleIntegral.omsDen M : Nat) : Int)
      have hKn : (radDiffBound M k hM).num = 4 * (xkAbs M k : Int) := by
        show (Q'.mkPos (4 * (xkAbs M k : Int)) (M * M) (Nat.mul_pos hM hM)).num
            = 4 * (xkAbs M k : Int)
        rw [Q'.mkPos_num]
      have hKd : ((radDiffBound M k hM).den : Int) = ((M * M : Nat) : Int) := by
        show ((Q'.mkPos (4 * (xkAbs M k : Int)) (M * M) (Nat.mul_pos hM hM)).den : Int)
            = ((M * M : Nat) : Int)
        rw [Q'.mkPos_den]
      rw [hKn, hKd, hMM]
      -- goal: (−4(2k+1−M))·(M²) ≤ (4|2k+1−M|)·(M²) ; |2k+1−M| = natAbs, −x ≤ |x|.
      have hMM0 : (0 : Int) ≤ ((M * M : Nat) : Int) := Int.natCast_nonneg _
      have hxa : (-(2 * (k : Int) + 1 - (M : Int))) ≤ (xkAbs M k : Int) := by
        have hh := Int.le_natAbs (a := -(2 * (k : Int) + 1 - (M : Int)))
        rw [Int.natAbs_neg] at hh
        exact hh
      have hnum : (-(4 * (2 * (k : Int) + 1 - (M : Int)))) ≤ 4 * (xkAbs M k : Int) := by
        have h4 : (4 : Int) * (-(2 * (k : Int) + 1 - (M : Int))) ≤ 4 * (xkAbs M k : Int) :=
          Int.mul_le_mul_of_nonneg_left hxa (by decide)
        have he : (-(4 * (2 * (k : Int) + 1 - (M : Int)))) = 4 * (-(2 * (k : Int) + 1 - (M : Int))) := by
          rw [Int.mul_neg]
        rw [he]; exact h4
      exact Int.mul_le_mul_of_nonneg_right hnum hMM0
    -- −q0 ≤ K
    have hq0_ge : (-q0) ≤ radDiffBound M k hM := by
      -- −q0 ≈ mkPos(4(2k+1−M)) (M²) ; ≤ mkPos(4|2k+1−M|)(M²)
      have hneg : (-q0) ≈ (Q'.mkPos (4 * (2 * (k : Int) + 1 - (M : Int)))
              (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM)) := by
        refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hq0eqv) ?_
        -- −(mkPos(−4x)(d)) ≈ mkPos(4x)(d)
        show (-(Q'.mkPos (-(4 * (2 * (k : Int) + 1 - (M : Int))))
                  (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM))).num
              * ((Q'.mkPos (4 * (2 * (k : Int) + 1 - (M : Int)))
                  (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM)).den : Int)
            = (Q'.mkPos (4 * (2 * (k : Int) + 1 - (M : Int)))
                  (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM)).num
              * ((-(Q'.mkPos (-(4 * (2 * (k : Int) + 1 - (M : Int))))
                  (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM))).den : Int)
        show (-((Q'.mkPos (-(4 * (2 * (k : Int) + 1 - (M : Int))))
                  (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM)).num))
              * ((Q'.mkPos (4 * (2 * (k : Int) + 1 - (M : Int)))
                  (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM)).den : Int)
            = (Q'.mkPos (4 * (2 * (k : Int) + 1 - (M : Int)))
                  (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM)).num
              * ((Q'.mkPos (-(4 * (2 * (k : Int) + 1 - (M : Int))))
                  (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM)).den : Int)
        rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den, Int.neg_neg]
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hneg) ?_
      show (Q'.mkPos (4 * (2 * (k : Int) + 1 - (M : Int)))
              (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM)).num
            * ((radDiffBound M k hM).den : Int)
          ≤ (radDiffBound M k hM).num
            * ((Q'.mkPos (4 * (2 * (k : Int) + 1 - (M : Int)))
                  (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM)).den : Int)
      rw [Q'.mkPos_num, Q'.mkPos_den]
      have hKn : (radDiffBound M k hM).num = 4 * (xkAbs M k : Int) := by
        show (Q'.mkPos (4 * (xkAbs M k : Int)) (M * M) (Nat.mul_pos hM hM)).num
            = 4 * (xkAbs M k : Int)
        rw [Q'.mkPos_num]
      have hKd : ((radDiffBound M k hM).den : Int) = ((M * M : Nat) : Int) := by
        show ((Q'.mkPos (4 * (xkAbs M k : Int)) (M * M) (Nat.mul_pos hM hM)).den : Int)
            = ((M * M : Nat) : Int)
        rw [Q'.mkPos_den]
      rw [hKn, hKd, hMM]
      have hMM0 : (0 : Int) ≤ ((M * M : Nat) : Int) := Int.natCast_nonneg _
      have hxa : (2 * (k : Int) + 1 - (M : Int)) ≤ (xkAbs M k : Int) := Int.le_natAbs
      have hnum : (4 * (2 * (k : Int) + 1 - (M : Int))) ≤ 4 * (xkAbs M k : Int) :=
        Int.mul_le_mul_of_nonneg_left hxa (by decide)
      exact Int.mul_le_mul_of_nonneg_right hnum hMM0
    -- assemble AbsLeRat R K from the constant-value bound
    refine ⟨?_, ?_⟩
    · refine CReal.leRat_of_eventually ⟨0, fun n _ => ?_⟩
      show (radp + (-radm)) ≤ radDiffBound M k hM
      exact hq0_le
    · refine CReal.leRat_of_eventually ⟨0, fun n _ => ?_⟩
      show (-(radp + (-radm))) ≤ radDiffBound M k hM
      exact hq0_ge
  -- (2) transfer R back to Q = s_+² + (−s_-²)  via radSq_diff_equiv (Equiv)
  have hQ : AbsLeRat
      (CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM (k + 1)))
        (CReal.neg (CReal.mul (bdyRadical M hM k) (bdyRadical M hM k))))
      (radDiffBound M k hM) := by
    refine AbsLeRat.of_equiv ?_ hR
    exact ChebOrthoRemainder.radSq_diff_equiv M hM k hk0 hkn hk1n
  -- (3) transfer Q to D·S via the per-approx difference-of-squares identity
  refine AbsLeRat.congr ?_ hQ
  intro n
  -- (D·S).approx n = (s_+_n + (−s_-_n))·(s_+_n + s_-_n)
  -- Q.approx n     = s_+_n·s_+_n + (−(s_-_n·s_-_n))
  show (((bdyRadical M hM (k + 1)).approx n + (-((bdyRadical M hM k).approx n)))
        * ((bdyRadical M hM (k + 1)).approx n + (bdyRadical M hM k).approx n))
      ≈ ((bdyRadical M hM (k + 1)).approx n * (bdyRadical M hM (k + 1)).approx n
          + (-((bdyRadical M hM k).approx n * (bdyRadical M hM k).approx n)))
  exact diffOfSquares_eqv ((bdyRadical M hM (k + 1)).approx n) ((bdyRadical M hM k).approx n)

/-! ## 4. THE SHARP reciprocal-free radical-difference bound -/

/-- `⌊√(4(j−1)j)⌋ > 0` for `j ≥ 2` (the radicand `4(j−1)j ≥ 8 ≥ 1`). -/
theorem isqrt_jdist_pos (j : Nat) (hj : 2 ≤ j) :
    0 < ChebOrthoMidpointEst.isqrt (4 * (j - 1) * j) := by
  have hpos : 0 < 4 * (j - 1) * j := by
    have h1 : 0 < j - 1 := by omega
    have h2 : 0 < j := by omega
    exact Nat.mul_pos (Nat.mul_pos (by decide) h1) h2
  have hge : 1 ≤ ChebOrthoMidpointEst.isqrt (4 * (j - 1) * j) :=
    ChebOrthoMidpointEst.isqrt_ge (m := 4 * (j - 1) * j) (K := 1) (by simpa using hpos)
  omega

/-- The SHARP reciprocal-free radical-difference bound `K / recipWitness =
4·|2k+1−M|/M² ÷ (⌊√(4(j−1)j)⌋/M) = (4·|2k+1−M|·M) / (M²·⌊√(4(j−1)j)⌋)`, `j = jdist M k`.
The denominator `M²·⌊√(4(j−1)j)⌋` is positive for an interior cell of distance
`j ≥ 2`. -/
def sharpBound (M k : Nat) (hM : 0 < M) (hj : 2 ≤ jdist M k) : Q' :=
  Q'.mkPos (4 * (xkAbs M k : Int) * (M : Int))
    (M * M * (ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k)))
    (Nat.mul_pos (Nat.mul_pos hM hM) (isqrt_jdist_pos (jdist M k) hj))

/-- `sharpBound ≥ 0` (numerator `4·|2k+1−M|·M ≥ 0`). -/
theorem sharpBound_nonneg (M k : Nat) (hM : 0 < M) (hj : 2 ≤ jdist M k) :
    (0 : Q') ≤ sharpBound M k hM hj := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (Q'.mkPos (4 * (xkAbs M k : Int) * (M : Int))
      (M * M * (ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k)))
      (Nat.mul_pos (Nat.mul_pos hM hM) (isqrt_jdist_pos (jdist M k) hj))).num
  rw [Q'.mkPos_num]
  have h1 : (0 : Int) ≤ 4 * (xkAbs M k : Int) :=
    Int.mul_nonneg (by decide) (Int.natCast_nonneg _)
  exact Int.mul_nonneg h1 (Int.natCast_nonneg _)

/-- `sharpBound · recipWitness ≈ radDiffBound`.  The product identity
`(4|x|·M)/(M²·a) · (a/M) = (4|x|·M·a)/(M²·a·M) ≈ (4|x|)/(M²) = radDiffBound`
(`a = ⌊√(4(j−1)j)⌋`), proved by cross-multiplication on the `mkPos` numerators and
denominators (`a > 0`, `M > 0` cancel). -/
theorem sharpBound_mul_recipWitness (M k : Nat) (hM : 0 < M) (hj : 2 ≤ jdist M k) :
    (sharpBound M k hM hj * recipWitness M (jdist M k) hM) ≈ radDiffBound M k hM := by
  -- name a := isqrt(4(j−1)j)
  let a : Nat := ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k)
  -- LHS = mkPos (4|x|·M) (M²·a) * mkPos a M
  --     num = (4|x|·M)·a,  den (cast) = (M²·a)·M
  -- RHS = mkPos (4|x|) (M²) :  num = 4|x|, den (cast) = M²
  -- eqv cross-mult:  ((4|x|·M)·a)·(M²) = (4|x|)·((M²·a)·M)
  show ((sharpBound M k hM hj * recipWitness M (jdist M k) hM).num)
        * ((radDiffBound M k hM).den : Int)
      = (radDiffBound M k hM).num
        * ((sharpBound M k hM hj * recipWitness M (jdist M k) hM).den : Int)
  have hLnum : (sharpBound M k hM hj * recipWitness M (jdist M k) hM).num
      = (4 * (xkAbs M k : Int) * (M : Int)) * (a : Int) := by
    show (sharpBound M k hM hj).num * (recipWitness M (jdist M k) hM).num
        = (4 * (xkAbs M k : Int) * (M : Int)) * (a : Int)
    rw [show (sharpBound M k hM hj).num = 4 * (xkAbs M k : Int) * (M : Int) from by
          show (Q'.mkPos (4 * (xkAbs M k : Int) * (M : Int)) _ _).num = _; rw [Q'.mkPos_num],
        show (recipWitness M (jdist M k) hM).num = (a : Int) from by
          show (Q'.mkPos ((a : Nat) : Int) M hM).num = (a : Int); rw [Q'.mkPos_num]]
  have hLden : ((sharpBound M k hM hj * recipWitness M (jdist M k) hM).den : Int)
      = ((M * M * a : Nat) : Int) * (M : Int) := by
    rw [Q'.mul_den_cast]
    rw [show (sharpBound M k hM hj).den = M * M * a from by
          show (Q'.mkPos _ (M * M * a) _).den = M * M * a; rw [Q'.mkPos_den],
        show (recipWitness M (jdist M k) hM).den = M from by
          show (Q'.mkPos _ M hM).den = M; rw [Q'.mkPos_den]]
  have hRnum : (radDiffBound M k hM).num = 4 * (xkAbs M k : Int) := by
    show (Q'.mkPos (4 * (xkAbs M k : Int)) (M * M) _).num = _; rw [Q'.mkPos_num]
  have hRden : ((radDiffBound M k hM).den : Int) = ((M * M : Nat) : Int) := by
    show ((Q'.mkPos (4 * (xkAbs M k : Int)) (M * M) _).den : Int) = _; rw [Q'.mkPos_den]
  rw [hLnum, hLden, hRnum, hRden]
  -- ((4|x|·M)·a)·(M²) = (4|x|)·((M²·a)·M)  : pure Int identity
  have hc1 : (((M * M * a : Nat)) : Int) = (M : Int) * (M : Int) * (a : Int) := by
    push_cast; rfl
  have hc2 : (((M * M : Nat)) : Int) = (M : Int) * (M : Int) := by push_cast; rfl
  rw [hc1, hc2]
  -- ((4|x|·M)·a)·(M·M) = (4|x|)·((M·M·a)·M)
  generalize (4 * (xkAbs M k : Int)) = x
  generalize (M : Int) = m
  generalize (a : Int) = aa
  -- x·m·aa·(m·m) = x·(m·m·aa·m)
  simp only [Int.mul_left_comm, Int.mul_comm]

/-- **THE SHARP RECIPROCAL-FREE RADICAL-DIFFERENCE BOUND.**  For an interior cell
`0 < k`, `k+1 < M` whose distance `j := jdist M k` satisfies `2 ≤ j`, the difference
of the two adjacent cell radicals `s_± = √(1 − b_{k±}²)` is two-sidedly bounded by the
SHARP reciprocal-free quotient

    `AbsLeRat (s_+ + (−s_-)) (sharpBound M k) = |s_+ − s_-| ≤ 4·|2k+1−M|δ / recipWitness`.

PROOF: apply the cancellation/division primitive `AbsLeRat.div_of_mul_ge` with
`D = s_+ − s_-`, `S = s_+ + s_-`, `K = radDiffBound M k = 4|2k+1−M|/M²`
(`radProdDiff_AbsLeRat`), `L = recipWitness M j` (pointwise lower bound
`interiorRadicalSum_ptwise`, positive by `recipWitness_pos`), and the concrete
quotient `KL = sharpBound M k` with `KL·L ≈ K` (`sharpBound_mul_recipWitness`).  This
is the residual #1 named in the interior off-diagonal assembly, now PROVED. -/
theorem bdyRadicalDiff_sharp (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hk1n : k + 1 < M) (hj : 2 ≤ jdist M k) :
    AbsLeRat (CReal.add (bdyRadical M hM (k + 1)) (CReal.neg (bdyRadical M hM k)))
      (sharpBound M k hM hj) := by
  have hkn : k < M := by omega
  refine AbsLeRat.div_of_mul_ge
    (D := CReal.add (bdyRadical M hM (k + 1)) (CReal.neg (bdyRadical M hM k)))
    (S := CReal.add (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
    (K := radDiffBound M k hM) (L := recipWitness M (jdist M k) hM)
    (KL := sharpBound M k hM hj)
    (radProdDiff_AbsLeRat M hM k hk0 hkn hk1n)
    (fun n => interiorRadicalSum_ptwise M hM k hk0 hkn hj n)
    (ChebOrthoInterior.recipWitness_pos M (jdist M k) hM hj)
    (sharpBound_nonneg M k hM hj)
    (sharpBound_mul_recipWitness M k hM hj)

end YMGap.Continuum.ChebOrthoCancelDiv

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `Q'.le_of_mul_le_mul_right_pos` — rational cancellation by a positive factor
    `a·c ≤ b·c → 0 < c → a ≤ b` (cross-multiplication + `Int.le_of_mul_le_mul_right`).
  * **`AbsLeRat.div_of_mul_ge`** — THE general cancellation/division primitive for the
    `AbsLeRat` two-sided value calculus: from `|D·S| ≤ K`, a pointwise lower bound
    `(∀ n, L ≤ S.approx n)`, `0 < L`, and a concrete rational quotient `KL ≥ 0` with
    `KL·L ≈ K`, conclude `|D| ≤ KL`.  Reciprocal-free; the two `leRat` directions use a
    constructive sign split on `D` (non-positive case free, positive case multiplies
    the lower bound and cancels `L > 0`).
  * `AbsLeRat.of_equiv` — `AbsLeRat` transfers across a `CReal.Equiv`.
  * `interiorRadicalSum_ptwise` — the POINTWISE reciprocal lower bound
    `recipWitness M j ≤ (s_+ + s_-).approx n` at every Heron index.
  * `diffOfSquares_eqv` — the pure-`Q'` identity `(a + (−b))·(a + b) ≈ a·a + (−(b·b))`.
  * `radProdDiff_AbsLeRat` — the squared-difference value bound
    `AbsLeRat ((s_+ − s_-)·(s_+ + s_-)) (4|2k+1−M|/M²)` via the exact
    `s_+² − s_-² = −4x_kδ` (`radSq_diff_equiv` + `bdyOneMinusSq_diff`) and the
    per-approximation difference-of-squares identity.
  * `sharpBound` / `sharpBound_nonneg` / `sharpBound_mul_recipWitness` — the explicit
    reciprocal-free quotient `(4|2k+1−M|·M)/(M²·⌊√(4(j−1)j)⌋)` and its defining product
    identity `sharpBound · recipWitness ≈ radDiffBound`.
  * **`bdyRadicalDiff_sharp`** — THE SHARP reciprocal-free radical-difference bound
    `AbsLeRat (s_+ + (−s_-)) (sharpBound M k)` (= `|s_+ − s_-| ≤ 4|2k+1−M|δ /
    recipWitness`) for an interior cell, by applying the division primitive to
    `radProdDiff_AbsLeRat` and `interiorRadicalSum_ptwise`.  The residual #1 of the
    interior off-diagonal assembly, now PROVED.

**NAMED-open (the honest residual — precisely).**
  * `ChebOrthoGradedClose.InteriorGradedRemainder e he` — the full interior per-cell
    two-sided estimate against `gradedRate = C(e)/(⌊√M⌋·jdist²)`.  With BOTH the
    √-Hölder radical difference and now the SHARP reciprocal-free radical difference
    PROVED, the residual is the NUMERIC second-order assembly: combine the
    product-difference split + the leading cancellation with the smooth-bracket-leg
    Lipschitz scale `Le e` (`R_poly`) and this sharp radical-leg bound (`R_rad`), then
    balance the exponents `4|x_k|δ/recipWitness ~ δ^{3/2}/j^{3/2} ≤ 1/(⌊√M⌋·j²)` to
    `gradedRate`.  Recorded precisely, NOT faked.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoCancelDiv.Q'.le_of_mul_le_mul_right_pos
#print axioms YMGap.Continuum.ChebOrthoCancelDiv.AbsLeRat.div_of_mul_ge
#print axioms YMGap.Continuum.ChebOrthoCancelDiv.AbsLeRat.of_equiv
#print axioms YMGap.Continuum.ChebOrthoCancelDiv.interiorRadicalSum_ptwise
#print axioms YMGap.Continuum.ChebOrthoCancelDiv.diffOfSquares_eqv
#print axioms YMGap.Continuum.ChebOrthoCancelDiv.radProdDiff_AbsLeRat
#print axioms YMGap.Continuum.ChebOrthoCancelDiv.sharpBound_nonneg
#print axioms YMGap.Continuum.ChebOrthoCancelDiv.sharpBound_mul_recipWitness
#print axioms YMGap.Continuum.ChebOrthoCancelDiv.bdyRadicalDiff_sharp
