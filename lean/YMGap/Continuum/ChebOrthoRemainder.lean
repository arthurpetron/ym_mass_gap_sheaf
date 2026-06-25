/-
# The PRODUCT-DIFFERENCE SPLIT of the real-boundary midpoint increment, toward the
# corrected per-cell midpoint estimate for the π-free off-diagonal Chebyshev-`U`
# orthogonality `∫_{−1}^1 U_e(x)√(1−x²) dx = 0`.

The companion construction reduces the even-order off-diagonal orthogonality to a
SINGLE per-cell midpoint estimate against a corrected (Lipschitz-absorbing) rate.
Each genuine adjusted cell is `orthTerm k + (GsampR(b_{k+1}) − GsampR(b_k))` where
the increment is `gIncrR k = GsampR(k+1) − GsampR(k)` and the antiderivative
samples are `GsampR(k) = ½·s_k·B_k` with `s_k = √(1 − b_k²)` the real cell radical
and `B_k = B_e(b_k)` the rational Chebyshev bracket.

## The product-difference split (the genuine separation of the two legs)

The increment is a PRODUCT DIFFERENCE `½·(s_+·B_+ − s_-·B_-)`.  The exact algebra

    `s_+·B_+ − s_-·B_- = ½(s_+ + s_-)(B_+ − B_-) + ½(s_+ − s_-)(B_+ + B_-)`

separates it into the SUM·DIFFERENCE legs: the `(s_+ + s_-)(B_+ − B_-)` leg
carries the smooth bracket finite-difference (no radical singularity), and the
`(s_+ − s_-)(B_+ + B_-)` leg carries the radical finite-difference (the √-Hölder
leg).  This is the EXACT rearrangement that feeds the leading-cancellation: the
leading term of the first leg is `s_k·B_e′(x_k)·h`, of the second `(−x_k/s_k)·h·B_e`,
and their `s`-cleared combination collapses by the bracket derivative identity.

This module proves that product-difference split as an EXACT rational identity at
every approximation index, lifts it to a `CReal` equivalence on the genuine real
increment `gIncrR`, and records the difference-of-squares relating the two cell
radicals' squares to their (closed-form) radicand difference.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `pdiff_abstract` — the EXACT abstract `Q'` product-difference identity
    `a·c + (−(b·d)) ≈ ½·((a+b)·(c+(−d))) + ½·((a+(−b))·(c+d))`, a pure rational
    `calc` over the congruence lemmas.  This is the algebraic heart of the split.
  * `pdiff_split_approx` — the split realised at the approximation level of the
    real increment: at every index `p`, the increment value `(gIncrR k).approx p`
    equals the product-difference split combination with
    `a = s_{k+1}.approx p`, `b = s_k.approx p`, `c = B_{k+1}`, `d = B_k`.
  * `gIncr_pdiff_split` — the `CReal` equivalence lifting `pdiff_split_approx`:
    the genuine real increment `gIncrR k` equals the sum·difference combination
    `½·(s_+ + s_-)·(B_+ − B_-) + ½·(s_+ − s_-)·(B_+ + B_-)` (all halves carried
    inside the bracket combination), the genuine separation of the two legs.
  * `bdyNum_diff` — the EXACT closed-form difference of the two cell radicands'
    Int numerators `bdyNum n (k+1) − bdyNum n k = −(4·(2k+1−n))` (the
    difference-of-squares `b_k² − b_{k+1}² = (x_k−δ)² − (x_k+δ)² = −4·x_k·δ` cleared
    of the common denominator `n²`, with `2k+1−n = n·x_k` and `δ = 1/n`).
  * `bdyOneMinusSq_diff` — the radicand difference as a `Q'` identity
    `(1 − b_{k+1}²) + (−(1 − b_k²)) ≈ mkPos (−(4·(2k+1−n))) n²`, the closed-form
    rational relating the two radicals' squares (the input to the radical leg).
  * `radSq_diff_equiv` — the `CReal` difference-of-squares of the genuine radicals
    `s_+·s_+ + (−(s_-·s_-)) ≈ ofQ'(1 − b_{k+1}²) + (−ofQ'(1 − b_k²))` for an
    INTERIOR cell `0 < k`, `k+1 < n`, via `sqrtFrom_sq_equiv` on each leg.

## What is NAMED-open (precisely — the SECOND-ORDER remainder)

  * `ChebOrthoMidpointCore.CorrectedPerCellBound e he` — the FULL per-cell estimate
    against the corrected rate.  The product-difference split (this module) plus the
    proved leading cancellation (`ChebOrthoCancel.leading_cancellation`) reduce the
    increment to its two finite-difference legs; the SINGLE remaining genuine content
    is the constructive bound on the SECOND-ORDER centered-difference REMAINDER of
    each leg (the bracket Taylor remainder, scale `Le e`, and the √-Hölder modulus
    of the radical leg, `radDiff_holder`), interior + boundary split balanced at
    `δ ≈ √h` to the corrected rate.  Recorded precisely, not faked.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoCancel
import YMGap.Continuum.ChebOrthoMidpointCore
import YMGap.Continuum.ChebOrthoMidpoint
import YMGap.Continuum.ChebUDClosure

namespace YMGap.Continuum.ChebOrthoRemainder

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.ChebOrthoEvenFTC
open YMGap.Continuum.ChebOrthoMidpoint
open YMGap.Continuum.ChebOrthoMidpointCore

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

/-! ## 0. Small additive abelian-group regrouping helpers (pure `Q'`-eqv)

The product-difference split, once both products are distributed, is an eight-term
additive cancellation.  We isolate the two reorderings it needs as standalone
`Q'`-eqv lemmas (pure `add_comm`/`add_assoc`/`add_neg_self` calc chains). -/

/-- `(a + b) + c ≈ (a + c) + b` (swap the last two summands). -/
theorem add_right_comm_eqv (a b c : Q') : ((a + b) + c) ≈ ((a + c) + b) := by
  calc (a + b) + c
      ≈ a + (b + c) := Q'.add_assoc_eqv a b c
    _ ≈ a + (c + b) := Q'.add_eqv_congr_left a (b + c) (c + b) (Q'.add_comm_eqv b c)
    _ ≈ (a + c) + b := Q'.eqv_symm (Q'.add_assoc_eqv a c b)

/-- The eight-term collection at the heart of `pdiff_abstract`.  With the canonical
products `p = a·c`, `q = a·d`, `r = b·c`, `s = b·d`,

    `(p + (−q) + (r + (−s))) + (p + q + ((−r) + (−s)))
       ≈ (p + (−s)) + (p + (−s))`,

the cross terms `−q + q` and `r + (−r)` cancelling.  Pure additive `Q'`-eqv. -/
theorem pdiff_collect (p q r s : Q') :
    (((p + (-q)) + (r + (-s))) + ((p + q) + ((-r) + (-s))))
      ≈ ((p + (-s)) + (p + (-s))) := by
  -- Flatten the left block:  (p + (−q) + (r + (−s)))
  --   = ((p + (−q)) + r) + (−s)
  have hL : ((p + (-q)) + (r + (-s)))
      ≈ (((p + (-q)) + r) + (-s)) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (p + (-q)) r (-s))
  -- Flatten the right block:  (p + q) + ((−r) + (−s))
  --   = ((p + q) + (−r)) + (−s)
  have hR : ((p + q) + ((-r) + (-s)))
      ≈ (((p + q) + (-r)) + (-s)) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (p + q) (-r) (-s))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hL hR) ?_
  -- Now LHS = (((p + (−q)) + r) + (−s)) + (((p + q) + (−r)) + (−s)).
  -- Reorder the left flat block to ((p + r) + (−q)) + (−s).
  have hL2 : (((p + (-q)) + r) + (-s))
      ≈ (((p + r) + (-q)) + (-s)) :=
    Q'.add_eqv_congr_right _ _ (-s) (add_right_comm_eqv p (-q) r)
  -- Reorder the right flat block to ((p + (−r)) + q) + (−s).
  have hR2 : (((p + q) + (-r)) + (-s))
      ≈ (((p + (-r)) + q) + (-s)) :=
    Q'.add_eqv_congr_right _ _ (-s) (add_right_comm_eqv p q (-r))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hL2 hR2) ?_
  -- Target left summand:  ((p + r) + (−q)) + (−s)  ≈ (p + (−s)) + (r + (−q))  …
  -- Strategy: prove each flat block ≈ (p + (−s)) + (extra) and pair the extras to 0.
  -- Concretely, regroup:
  --   ((p + r) + (−q)) + (−s)        with the right block
  --   ((p + (−r)) + q) + (−s)
  -- summed; the `r + (−r)` and `(−q) + q` cancel, leaving (p+(−s)) + (p+(−s)).
  -- Build the canonical form  ((p + (−s)) + r) + (−q) for the left block:
  have hLc : (((p + r) + (-q)) + (-s)) ≈ (((p + (-s)) + r) + (-q)) := by
    calc ((p + r) + (-q)) + (-s)
        ≈ ((p + r) + (-s)) + (-q) := add_right_comm_eqv (p + r) (-q) (-s)
      _ ≈ ((p + (-s)) + r) + (-q) :=
          Q'.add_eqv_congr_right _ _ (-q) (add_right_comm_eqv p r (-s))
  -- and  ((p + (−s)) + (−r)) + q  for the right block:
  have hRc : (((p + (-r)) + q) + (-s)) ≈ (((p + (-s)) + (-r)) + q) := by
    calc ((p + (-r)) + q) + (-s)
        ≈ ((p + (-r)) + (-s)) + q := add_right_comm_eqv (p + (-r)) q (-s)
      _ ≈ ((p + (-s)) + (-r)) + q :=
          Q'.add_eqv_congr_right _ _ q (add_right_comm_eqv p (-r) (-s))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hLc hRc) ?_
  -- Now: (((p+(−s)) + r) + (−q)) + (((p+(−s)) + (−r)) + q)
  --       ≈ (p+(−s)) + (p+(−s)).
  -- Reassociate to  P+P + (r + (−r)) + ((−q) + q) via additive shuffles, P := p+(−s).
  have ha1 : (((p + (-s)) + r) + (-q)) ≈ ((p + (-s)) + (r + (-q))) :=
    Q'.add_assoc_eqv (p + (-s)) r (-q)
  have ha2 : (((p + (-s)) + (-r)) + q) ≈ ((p + (-s)) + ((-r) + q)) :=
    Q'.add_assoc_eqv (p + (-s)) (-r) q
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ha1 ha2) ?_
  -- (P + X) + (P + Y) ≈ (P + P) + (X + Y)  with X = r+(−q), Y = (−r)+q.
  have hswap : (((p + (-s)) + (r + (-q))) + ((p + (-s)) + ((-r) + q)))
      ≈ (((p + (-s)) + (p + (-s))) + ((r + (-q)) + ((-r) + q))) := by
    calc ((p + (-s)) + (r + (-q))) + ((p + (-s)) + ((-r) + q))
        ≈ (((p + (-s)) + (r + (-q))) + (p + (-s))) + ((-r) + q) :=
          Q'.eqv_symm (Q'.add_assoc_eqv ((p + (-s)) + (r + (-q))) (p + (-s)) ((-r) + q))
      _ ≈ (((p + (-s)) + (p + (-s))) + (r + (-q))) + ((-r) + q) :=
          Q'.add_eqv_congr_right _ _ _ (add_right_comm_eqv (p + (-s)) (r + (-q)) (p + (-s)))
      _ ≈ ((p + (-s)) + (p + (-s))) + ((r + (-q)) + ((-r) + q)) :=
          Q'.add_assoc_eqv ((p + (-s)) + (p + (-s))) (r + (-q)) ((-r) + q)
  refine Q'.eqv_trans _ _ _ hswap ?_
  -- The cross block (r + (−q)) + ((−r) + q) ≈ 0.
  have hcross : ((r + (-q)) + ((-r) + q)) ≈ (0 : Q') := by
    -- = ((r + (−q)) + (−r)) + q ≈ ((r + (−r)) + (−q)) + q ≈ (0 + (−q)) + q
    calc (r + (-q)) + ((-r) + q)
        ≈ ((r + (-q)) + (-r)) + q :=
          Q'.eqv_symm (Q'.add_assoc_eqv (r + (-q)) (-r) q)
      _ ≈ ((r + (-r)) + (-q)) + q :=
          Q'.add_eqv_congr_right _ _ q (add_right_comm_eqv r (-q) (-r))
      _ ≈ ((0 : Q') + (-q)) + q :=
          Q'.add_eqv_congr_right _ _ q
            (Q'.add_eqv_congr_right _ _ (-q) (Q'.add_neg_self_eqv r))
      _ ≈ (-q) + q := Q'.add_eqv_congr_right _ _ q (QPoly.q_zero_add_eqv (-q))
      _ ≈ q + (-q) := Q'.add_comm_eqv (-q) q
      _ ≈ (0 : Q') := Q'.add_neg_self_eqv q
  -- (P + P) + 0 ≈ P + P.
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hcross) ?_
  exact QPoly.q_add_zero_eqv ((p + (-s)) + (p + (-s)))

/-! ## 1. The EXACT abstract product-difference identity

`a·c − b·d = ½(a+b)(c−d) + ½(a−b)(c+d)`.  Expanding the RHS:
`½[(ac − ad + bc − bd) + (ac + ad − bc − bd)] = ½[2ac − 2bd] = ac − bd`.
A pure rational `calc` over the `Q'`-ring congruence lemmas. -/

/-- **THE PRODUCT-DIFFERENCE IDENTITY (abstract).**  For any rationals `a, b, c, d`,

    `a·c + (−(b·d)) ≈ ½·((a+b)·(c+(−d))) + ½·((a+(−b))·(c+d))`.

This is the EXACT separation `s_+B_+ − s_-B_- = ½(s_++s_-)(B_+−B_-)
+ ½(s_+−s_-)(B_++B_-)` of the midpoint increment into its smooth-bracket and
radical finite-difference legs.  Division-free pure `Q'`-ring `calc`. -/
theorem pdiff_abstract (a b c d : Q') :
    (a * c + (-(b * d)))
      ≈ ((Q'.mkPos 1 2 (by decide)) * ((a + b) * (c + (-d)))
          + (Q'.mkPos 1 2 (by decide)) * ((a + (-b)) * (c + d))) := by
  refine Q'.eqv_symm ?_
  -- Distribute both products.
  have hP : ((a + b) * (c + (-d)))
      ≈ ((a * c + a * (-d)) + (b * c + b * (-d))) := by
    calc (a + b) * (c + (-d))
        ≈ a * (c + (-d)) + b * (c + (-d)) := Cheb.add_mul_eqv a b (c + (-d))
      _ ≈ (a * c + a * (-d)) + (b * c + b * (-d)) :=
          Q'.add_eqv_congr' (Q'.mul_add_eqv a c (-d)) (Q'.mul_add_eqv b c (-d))
  have hQ : ((a + (-b)) * (c + d))
      ≈ ((a * c + a * d) + ((-b) * c + (-b) * d)) := by
    calc (a + (-b)) * (c + d)
        ≈ a * (c + d) + (-b) * (c + d) := Cheb.add_mul_eqv a (-b) (c + d)
      _ ≈ (a * c + a * d) + ((-b) * c + (-b) * d) :=
          Q'.add_eqv_congr' (Q'.mul_add_eqv a c d) (Q'.mul_add_eqv (-b) c d)
  -- ½·P + ½·Q ≈ ½·(P + Q).
  have hhalf : ((Q'.mkPos 1 2 (by decide)) * ((a + b) * (c + (-d)))
      + (Q'.mkPos 1 2 (by decide)) * ((a + (-b)) * (c + d)))
        ≈ ((Q'.mkPos 1 2 (by decide)) * (((a + b) * (c + (-d))) + ((a + (-b)) * (c + d)))) :=
    Q'.eqv_symm (Q'.mul_add_eqv (Q'.mkPos 1 2 (by decide))
      ((a + b) * (c + (-d))) ((a + (-b)) * (c + d)))
  refine Q'.eqv_trans _ _ _ hhalf ?_
  -- ½·(P+Q) ≈ ½·(distributed P + distributed Q).
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr' hP hQ)) ?_
  -- Canonicalise the signed products, then collect the eight terms.
  have hbig :
      (((a * c + a * (-d)) + (b * c + b * (-d)))
        + ((a * c + a * d) + ((-b) * c + (-b) * d)))
        ≈ ((a * c + (-(b * d))) + (a * c + (-(b * d)))) := by
    -- a·(−d) ≈ −(a·d), b·(−d) ≈ −(b·d), (−b)·c ≈ −(b·c), (−b)·d ≈ −(b·d).
    have e1 : a * (-d) ≈ (-(a * d)) := Q'.mul_neg_eqv a d
    have e2 : b * (-d) ≈ (-(b * d)) := Q'.mul_neg_eqv b d
    have e3 : (-b) * c ≈ (-(b * c)) := Q'.neg_mul_eqv b c
    have e4 : (-b) * d ≈ (-(b * d)) := Q'.neg_mul_eqv b d
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr_left _ _ _ e1)
          (Q'.add_eqv_congr_left _ _ _ e2))
        (Q'.add_eqv_congr'
          (Q'.eqv_refl _)
          (Q'.add_eqv_congr' e3 e4))) ?_
    -- Now exactly the `pdiff_collect` shape with p=a·c, q=a·d, r=b·c, s=b·d.
    exact pdiff_collect (a * c) (a * d) (b * c) (b * d)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hbig) ?_
  -- ½·(z + z) ≈ z with z = a·c + (−(b·d)).
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (ChebOrthoCancel.two_mul_eqv (a * c + (-(b * d)))))) ?_
  -- ½·(2·z) ≈ z.
  calc (Q'.mkPos 1 2 (by decide)) * ((2 : Q') * (a * c + (-(b * d))))
      ≈ ((Q'.mkPos 1 2 (by decide)) * (2 : Q')) * (a * c + (-(b * d))) :=
        Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    _ ≈ (1 : Q') * (a * c + (-(b * d))) :=
        Q'.mul_eqv_congr_right _ _ _ (by decide)
    _ ≈ (a * c + (-(b * d))) := Q'.one_mul_eqv _

/-- Factor `½` out of a product-difference: `½·u + (−(½·v)) ≈ ½·(u + (−v))`.
The two `½·…` terms of the real increment combine into the single `½·(…)` shape
fed to `pdiff_abstract`.  Pure `Q'`-eqv. -/
theorem half_factor (u v : Q') :
    ((Q'.mkPos 1 2 (by decide)) * u + (-((Q'.mkPos 1 2 (by decide)) * v)))
      ≈ ((Q'.mkPos 1 2 (by decide)) * (u + (-v))) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.mul_neg_eqv (Q'.mkPos 1 2 (by decide)) v))) ?_
  exact Q'.eqv_symm (Q'.mul_add_eqv (Q'.mkPos 1 2 (by decide)) u (-v))

/-! ## 2. The split realised on the genuine real increment `gIncrR`

The increment `gIncrR e he n hn k = GsampR(k+1) + (−GsampR(k))` with
`GsampR(j) = ½·s_j·B_j` (`s_j = √(1−b_j²)`, `B_j = B_e(b_j)`).  At every approx
index its value is `½·(a·c) + (−(½·(b·d)))` with `a = s_{k+1}.approx p`,
`b = s_k.approx p`, `c = B_{k+1}`, `d = B_k`; combining the two halves
(`half_factor`) and applying `pdiff_abstract` gives the product-difference split. -/

/-- Abbreviations for the four split data at cell `k` (the two real radical
approximations and the two rational brackets). -/
private def sPlus (n : Nat) (hn : 0 < n) (k : Nat) : CReal := bdyRadical n hn (k + 1)
private def sMinus (n : Nat) (hn : 0 < n) (k : Nat) : CReal := bdyRadical n hn k
private def bPlus (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) : Q' :=
  Gbracket e he (bdyPoint n hn (k + 1))
private def bMinus (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) : Q' :=
  Gbracket e he (bdyPoint n hn k)

/-- **The product-difference split, RHS as a genuine `CReal`.**
`splitCReal k := ½·( ½·(s_+ + s_-)·(B_+ − B_-) + ½·(s_+ − s_-)·(B_+ + B_-) )`
(the two sum·difference legs at half weight, then the overall `½` of the increment;
the rational brackets via `ofQ'`).  The outer `½` is the `½` of
`gIncrR = ½·(s_+B_+ − s_-B_-)`. -/
def splitCReal (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) : CReal :=
  CReal.mul (CReal.ofQ' (Q'.mkPos 1 2 (by decide)))
    (CReal.add
      (CReal.mul (CReal.ofQ' (Q'.mkPos 1 2 (by decide)))
        (CReal.mul (CReal.add (sPlus n hn k) (sMinus n hn k))
          (CReal.add (CReal.ofQ' (bPlus e he n hn k))
            (CReal.neg (CReal.ofQ' (bMinus e he n hn k))))))
      (CReal.mul (CReal.ofQ' (Q'.mkPos 1 2 (by decide)))
        (CReal.mul (CReal.add (sPlus n hn k) (CReal.neg (sMinus n hn k)))
          (CReal.add (CReal.ofQ' (bPlus e he n hn k))
            (CReal.ofQ' (bMinus e he n hn k))))))

/-- **The split at the approximation level.**  At every index `p`,
`(gIncrR e he n hn k).approx p ≈ (splitCReal e he n hn k).approx p`.  The LHS is
`½·(a·c) + (−(½·(b·d)))`; `half_factor` combines the halves to `½·(a·c + (−(b·d)))`,
and `pdiff_abstract` rewrites it as the two sum·difference legs (which is exactly
the RHS approx). -/
theorem pdiff_split_approx (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) (p : Nat) :
    ((gIncrR e he n hn k).approx p) ≈ ((splitCReal e he n hn k).approx p) := by
  -- Name the four data.
  -- a = (bdyRadical (k+1)).approx p, b = (bdyRadical k).approx p,
  -- c = Gbracket(bdyPoint (k+1)), d = Gbracket(bdyPoint k).
  -- LHS approx (definitional): ½·(a·c) + (−(½·(b·d))).
  -- RHS approx (definitional): ½·((a+b)·(c+(−d))) + ½·((a+(−b))·(c+d)).
  have hLHS :
      ((gIncrR e he n hn k).approx p)
        = ((Q'.mkPos 1 2 (by decide))
              * ((bdyRadical n hn (k + 1)).approx p * Gbracket e he (bdyPoint n hn (k + 1)))
            + (-((Q'.mkPos 1 2 (by decide))
              * ((bdyRadical n hn k).approx p * Gbracket e he (bdyPoint n hn k))))) := rfl
  have hRHS :
      ((splitCReal e he n hn k).approx p)
        = ((Q'.mkPos 1 2 (by decide))
            * ((Q'.mkPos 1 2 (by decide))
                * (((bdyRadical n hn (k + 1)).approx p + (bdyRadical n hn k).approx p)
                    * (Gbracket e he (bdyPoint n hn (k + 1))
                        + (-(Gbracket e he (bdyPoint n hn k)))))
              + (Q'.mkPos 1 2 (by decide))
                * (((bdyRadical n hn (k + 1)).approx p + (-((bdyRadical n hn k).approx p)))
                    * (Gbracket e he (bdyPoint n hn (k + 1))
                        + Gbracket e he (bdyPoint n hn k))))) := rfl
  rw [hLHS, hRHS]
  -- combine halves: ½·(a·c) + (−(½·(b·d))) ≈ ½·(a·c + (−(b·d))).
  refine Q'.eqv_trans _ _ _
    (half_factor
      ((bdyRadical n hn (k + 1)).approx p * Gbracket e he (bdyPoint n hn (k + 1)))
      ((bdyRadical n hn k).approx p * Gbracket e he (bdyPoint n hn k))) ?_
  -- then ½·(a·c + (−(b·d))) ≈ ½·(split) via pdiff_abstract under the outer ½.
  exact Q'.mul_eqv_congr_left _ _ _
    (pdiff_abstract
      ((bdyRadical n hn (k + 1)).approx p) ((bdyRadical n hn k).approx p)
      (Gbracket e he (bdyPoint n hn (k + 1))) (Gbracket e he (bdyPoint n hn k)))

/-- **THE PRODUCT-DIFFERENCE SPLIT (CReal level).**  The genuine real-boundary
midpoint increment equals its sum·difference separation:

    `gIncrR e he n hn k
       ≈ ½·(s_+ + s_-)·(B_+ − B_-) + ½·(s_+ − s_-)·(B_+ + B_-)`,

with `s_± = √(1 − b_{k±}²)` the genuine cell radicals and `B_± = B_e(b_{k±})` the
rational brackets.  Lifts `pdiff_split_approx` via `Equiv_of_approx_eqv`.  This is
the EXACT separation of the increment into the smooth-bracket leg (the
`(s_+ + s_-)(B_+ − B_-)` term, no radical singularity) and the radical leg (the
`(s_+ − s_-)(B_+ + B_-)` term, the √-Hölder leg). -/
theorem gIncr_pdiff_split (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) :
    CReal.Equiv (gIncrR e he n hn k) (splitCReal e he n hn k) :=
  SumOfSquares.Equiv_of_approx_eqv (fun p => pdiff_split_approx e he n hn k p)

/-! ## 3. The difference-of-squares relating the two cell radicals

The two adjacent cell radicands `1 − b_{k+1}²` and `1 − b_k²` share the common
denominator `n²`; their Int numerators `bdyNum` differ by the EXACT closed form
`−4·(2k+1−n)` (the difference-of-squares `b_k² − b_{k+1}² = −4·x_k·δ` with
`2k+1−n = n·x_k` and `δ = 1/n` cleared of `n²`).  Lifted to `Q'`, this is the
radicand difference fed to the √-Hölder radical leg; lifted to `CReal` (via
`sqrtFrom_sq_equiv`), it relates the two radicals' SQUARES. -/

/-- Abstract square-difference: `A·A − (A+2)·(A+2) = −(4·(A+1))` for any `Int A`.
Expand `(A+2)·(A+2) = A·A + 4·A + 4` via core `Int` distribution, then `omega`. -/
theorem int_sq_step_diff (A : Int) :
    A * A - (A + 2) * (A + 2) = -(4 * (A + 1)) := by
  have h1 : (A + 2) * (A + 2) = A * (A + 2) + 2 * (A + 2) := Int.add_mul A 2 (A + 2)
  have h2 : A * (A + 2) = A * A + A * 2 := Int.mul_add A A 2
  have h3 : 2 * (A + 2) = 2 * A + 2 * 2 := Int.mul_add 2 A 2
  omega

/-- **The EXACT closed-form radicand-numerator difference.**
`bdyNum n (k+1) − bdyNum n k = −(4·(2k+1−n))` (`Int`).  Since
`bdyNum n j = n² − (2j−n)²`, the `n²` cancels and the difference is the
square-difference `(2k−n)² − (2(k+1)−n)²`, which by `int_sq_step_diff` (with
`A = 2k−n`, `A+2 = 2(k+1)−n`) is `−4·(2k−n+1) = −4·(2k+1−n)`. -/
theorem bdyNum_diff (n k : Nat) :
    bdyNum n (k + 1) - bdyNum n k = -(4 * (2 * (k : Int) + 1 - (n : Int))) := by
  -- unfold both bdyNum (note bdyNum n j = n*n − (2j−n)*(2j−n))
  show ((n : Int) * (n : Int)
        - (2 * ((k + 1 : Nat) : Int) - (n : Int)) * (2 * ((k + 1 : Nat) : Int) - (n : Int)))
      - ((n : Int) * (n : Int)
        - (2 * (k : Int) - (n : Int)) * (2 * (k : Int) - (n : Int)))
    = -(4 * (2 * (k : Int) + 1 - (n : Int)))
  -- rewrite 2·(k+1) − n = (2k − n) + 2
  have hcast : (2 * ((k + 1 : Nat) : Int) - (n : Int))
      = ((2 * (k : Int) - (n : Int)) + 2) := by push_cast; omega
  rw [hcast]
  -- now the goal is  (n² − (A+2)²) − (n² − A²) = −(4·(A+1))  with A = 2k − n.
  have hstep := int_sq_step_diff (2 * (k : Int) - (n : Int))
  -- the `2k+1−n` on the RHS equals A+1
  omega

/-- The common-denominator difference as a `Q'` identity.
`(1 − b_{k+1}²) + (−(1 − b_k²)) ≈ mkPos (−(4·(2k+1−n))) n²` for an INTERIOR pair
`0 < k`, `k < n`, `0 < k+1`, `k+1 < n`.  Both radicands have denominator
`omsDen n = n²`; the numerator difference is `bdyNum_diff`. -/
theorem bdyOneMinusSq_diff (n k : Nat) (hn : 0 < n)
    (hk0 : 0 < k) (hkn : k < n) (hk1n : k + 1 < n) :
    (bdyOneMinusSq n (k + 1) hn (Nat.succ_pos k) hk1n
        + (-(bdyOneMinusSq n k hn hk0 hkn)))
      ≈ (Q'.mkPos (-(4 * (2 * (k : Int) + 1 - (n : Int))))
            (SemicircleIntegral.omsDen n) (SemicircleIntegral.omsDen_pos hn)) := by
  -- Both summands are `mkPos (bdyNum …) (omsDen n)`; abbreviate D := omsDen n,
  -- N1 := bdyNum n (k+1), N2 := bdyNum n k.  The sum `mkPos N1 D + (−mkPos N2 D)`
  -- has (definitionally) num = N1·D + (−N2)·D and den (cast) = D·D.
  -- The eqv cross-multiplication goal:
  --   (N1·D + (−N2)·D)·D = (−(4·(2k+1−n)))·(D·D).
  have hdiff := bdyNum_diff n k
  -- the eqv, by cross-multiplication
  show ((bdyOneMinusSq n (k + 1) hn (Nat.succ_pos k) hk1n
          + (-(bdyOneMinusSq n k hn hk0 hkn))).num)
        * ((Q'.mkPos (-(4 * (2 * (k : Int) + 1 - (n : Int))))
              (SemicircleIntegral.omsDen n) (SemicircleIntegral.omsDen_pos hn)).den : Int)
      = (Q'.mkPos (-(4 * (2 * (k : Int) + 1 - (n : Int))))
              (SemicircleIntegral.omsDen n) (SemicircleIntegral.omsDen_pos hn)).num
        * (((bdyOneMinusSq n (k + 1) hn (Nat.succ_pos k) hk1n
              + (-(bdyOneMinusSq n k hn hk0 hkn))).den) : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  -- compute the sum's num (definitional) and den (cast via add_den_cast)
  have hnum :
      (bdyOneMinusSq n (k + 1) hn (Nat.succ_pos k) hk1n
          + (-(bdyOneMinusSq n k hn hk0 hkn))).num
        = bdyNum n (k + 1) * (SemicircleIntegral.omsDen n : Int)
          + (-(bdyNum n k)) * (SemicircleIntegral.omsDen n : Int) := by
    unfold bdyOneMinusSq
    -- expose the Q'-add num formula:  (x + y).num = x.num·y.den + y.num·x.den
    show (Q'.mkPos (bdyNum n (k + 1)) (SemicircleIntegral.omsDen n)
              (SemicircleIntegral.omsDen_pos hn)).num
          * (((-(Q'.mkPos (bdyNum n k) (SemicircleIntegral.omsDen n)
              (SemicircleIntegral.omsDen_pos hn))).den : Nat) : Int)
        + (-(Q'.mkPos (bdyNum n k) (SemicircleIntegral.omsDen n)
              (SemicircleIntegral.omsDen_pos hn))).num
          * (((Q'.mkPos (bdyNum n (k + 1)) (SemicircleIntegral.omsDen n)
              (SemicircleIntegral.omsDen_pos hn)).den : Nat) : Int)
        = bdyNum n (k + 1) * (SemicircleIntegral.omsDen n : Int)
          + (-(bdyNum n k)) * (SemicircleIntegral.omsDen n : Int)
    rw [Q'.neg_den, Q'.mkPos_den, Q'.mkPos_den, Q'.mkPos_num]
    show bdyNum n (k + 1) * (SemicircleIntegral.omsDen n : Int)
        + (-(Q'.mkPos (bdyNum n k) (SemicircleIntegral.omsDen n)
              (SemicircleIntegral.omsDen_pos hn)).num) * (SemicircleIntegral.omsDen n : Int)
        = bdyNum n (k + 1) * (SemicircleIntegral.omsDen n : Int)
          + (-(bdyNum n k)) * (SemicircleIntegral.omsDen n : Int)
    rw [Q'.mkPos_num]
  have hden :
      (((bdyOneMinusSq n (k + 1) hn (Nat.succ_pos k) hk1n
            + (-(bdyOneMinusSq n k hn hk0 hkn))).den) : Int)
        = (SemicircleIntegral.omsDen n : Int) * (SemicircleIntegral.omsDen n : Int) := by
    rw [Q'.add_den_cast, Q'.neg_den]
    unfold bdyOneMinusSq
    rw [Q'.mkPos_den, Q'.mkPos_den]
  rw [hnum, hden]
  -- goal: (N1·D + (−N2)·D)·D = (−(4·(2k+1−n)))·(D·D), with N1−N2 = −(4·…).
  -- factor the LHS into (N1 − N2)·(D·D), then rewrite by hdiff.
  have hfact :
      (bdyNum n (k + 1) * (SemicircleIntegral.omsDen n : Int)
        + (-(bdyNum n k)) * (SemicircleIntegral.omsDen n : Int))
          * (SemicircleIntegral.omsDen n : Int)
      = (bdyNum n (k + 1) - bdyNum n k)
          * ((SemicircleIntegral.omsDen n : Int) * (SemicircleIntegral.omsDen n : Int)) := by
    have e1 : (-(bdyNum n k)) * (SemicircleIntegral.omsDen n : Int)
        = -(bdyNum n k * (SemicircleIntegral.omsDen n : Int)) := by rw [Int.neg_mul]
    have e2 : (bdyNum n (k + 1) * (SemicircleIntegral.omsDen n : Int)
        + (-(bdyNum n k)) * (SemicircleIntegral.omsDen n : Int))
        = (bdyNum n (k + 1) - bdyNum n k) * (SemicircleIntegral.omsDen n : Int) := by
      rw [Int.sub_mul, e1, Int.sub_eq_add_neg]
    rw [e2, Int.mul_assoc]
  rw [hfact, hdiff]

/-- Additive shuffle `(p + q) + (e₁ + e₂) ≈ (p + e₁) + (q + e₂)`. -/
theorem add_shuffle (p q e1 e2 : Q') :
    (((p + q) + (e1 + e2))) ≈ (((p + e1) + (q + e2))) := by
  calc (p + q) + (e1 + e2)
      ≈ p + (q + (e1 + e2)) := Q'.add_assoc_eqv p q (e1 + e2)
    _ ≈ p + ((q + e1) + e2) :=
        Q'.add_eqv_congr_left p _ _ (Q'.eqv_symm (Q'.add_assoc_eqv q e1 e2))
    _ ≈ p + ((e1 + q) + e2) :=
        Q'.add_eqv_congr_left p _ _ (Q'.add_eqv_congr_right _ _ e2 (Q'.add_comm_eqv q e1))
    _ ≈ p + (e1 + (q + e2)) :=
        Q'.add_eqv_congr_left p _ _ (Q'.add_assoc_eqv e1 q e2)
    _ ≈ (p + e1) + (q + e2) := Q'.eqv_symm (Q'.add_assoc_eqv p e1 (q + e2))

/-- **`add (neg ·)` is `Equiv`-congruent** (pointwise: `add`/`neg` act approx-wise).
`Equiv A A' → Equiv B B' → Equiv (add A (neg B)) (add A' (neg B'))`. -/
theorem addNeg_Equiv_congr {A A' B B' : CReal}
    (hA : CReal.Equiv A A') (hB : CReal.Equiv B B') :
    CReal.Equiv (CReal.add A (CReal.neg B)) (CReal.add A' (CReal.neg B')) := by
  intro ε hε
  have hhε : (0 : Q') < (Q'.mkPos 1 2 (by decide)) * ε :=
    ExpNeg.half_mul_pos ε hε
  -- use ε/2 on each leg
  obtain ⟨NA, hNA⟩ := hA ((Q'.mkPos 1 2 (by decide)) * ε) hhε
  obtain ⟨NB, hNB⟩ := hB ((Q'.mkPos 1 2 (by decide)) * ε) hhε
  refine ⟨max NA NB, fun n hn => ?_⟩
  have hnA : NA ≤ n := Nat.le_trans (Nat.le_max_left NA NB) hn
  have hnB : NB ≤ n := Nat.le_trans (Nat.le_max_right NA NB) hn
  obtain ⟨hA1, hA2⟩ := hNA n hnA
  obtain ⟨hB1, hB2⟩ := hNB n hnB
  -- (add A (neg B)).approx n = A_n + (−B_n)  (rfl).
  show (A.approx n + (-(B.approx n))) ≤ (A'.approx n + (-(B'.approx n))) + ε
      ∧ (A'.approx n + (-(B'.approx n))) ≤ (A.approx n + (-(B.approx n))) + ε
  -- ½ε + ½ε = ε
  have hsum : ((Q'.mkPos 1 2 (by decide)) * ε + (Q'.mkPos 1 2 (by decide)) * ε) ≈ ε := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Cheb.add_mul_eqv (Q'.mkPos 1 2 (by decide)) (Q'.mkPos 1 2 (by decide)) ε)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ ε (by decide : ((Q'.mkPos 1 2 (by decide))
        + (Q'.mkPos 1 2 (by decide))) ≈ (1 : Q'))) ?_
    exact Q'.one_mul_eqv ε
  refine ⟨?_, ?_⟩
  · -- A_n + (−B_n) ≤ (A'_n + (−B'_n)) + ε
    -- from A_n ≤ A'_n + ½ε and B'_n ≤ B_n + ½ε (i.e. −B_n ≤ −B'_n + ½ε).
    have hnegB : (-(B.approx n)) ≤ (-(B'.approx n)) + (Q'.mkPos 1 2 (by decide)) * ε :=
      Q'.neg_le_neg_add hB2
    have hadd := Q'.add_le_add hA1 hnegB
    -- hadd : A_n + (−B_n) ≤ (A'_n + ½ε) + ((−B'_n) + ½ε)
    refine Q'.le_trans' _ _ _ hadd ?_
    -- (A'_n + ½ε) + ((−B'_n) + ½ε) ≈ (A'_n + (−B'_n)) + ε
    refine Q'.ge_of_eqv ?_
    calc ((A'.approx n + (-(B'.approx n))) + ε)
        ≈ (A'.approx n + (-(B'.approx n)))
            + ((Q'.mkPos 1 2 (by decide)) * ε + (Q'.mkPos 1 2 (by decide)) * ε) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm hsum)
      _ ≈ (A'.approx n + (Q'.mkPos 1 2 (by decide)) * ε)
            + ((-(B'.approx n)) + (Q'.mkPos 1 2 (by decide)) * ε) :=
          add_shuffle (A'.approx n) (-(B'.approx n))
            ((Q'.mkPos 1 2 (by decide)) * ε) ((Q'.mkPos 1 2 (by decide)) * ε)
  · have hnegB : (-(B'.approx n)) ≤ (-(B.approx n)) + (Q'.mkPos 1 2 (by decide)) * ε :=
      Q'.neg_le_neg_add hB1
    have hadd := Q'.add_le_add hA2 hnegB
    refine Q'.le_trans' _ _ _ hadd ?_
    refine Q'.ge_of_eqv ?_
    calc ((A.approx n + (-(B.approx n))) + ε)
        ≈ (A.approx n + (-(B.approx n)))
            + ((Q'.mkPos 1 2 (by decide)) * ε + (Q'.mkPos 1 2 (by decide)) * ε) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm hsum)
      _ ≈ (A.approx n + (Q'.mkPos 1 2 (by decide)) * ε)
            + ((-(B.approx n)) + (Q'.mkPos 1 2 (by decide)) * ε) :=
          add_shuffle (A.approx n) (-(B.approx n))
            ((Q'.mkPos 1 2 (by decide)) * ε) ((Q'.mkPos 1 2 (by decide)) * ε)

/-- For an INTERIOR index the genuine radical is the `sqrtFrom` of its radicand
(unfolding the two `dif_pos` guards of `bdyRadical`). -/
theorem bdyRadical_interior (n : Nat) (hn : 0 < n) (k : Nat) (hk0 : 0 < k) (hkn : k < n) :
    bdyRadical n hn k
      = CReal.sqrtFrom (bdyOneMinusSq n k hn hk0 hkn) (SemicircleIntegral.nodeLB n hn)
          (bdyOneMinusSq_pos hn hk0 hkn) (SemicircleIntegral.nodeLB_pos hn)
          (bdyLB_sq_le hn hk0 hkn) := by
  unfold bdyRadical
  rw [dif_pos hk0, dif_pos hkn]

/-- **The `CReal` difference-of-squares of the two cell radicals.**  For an
INTERIOR pair `0 < k`, `k+1 < n` (so both `b_k`, `b_{k+1}` are interior),

    `s_+·s_+ + (−(s_-·s_-)) ≈ ofQ'(1 − b_{k+1}²) + (−ofQ'(1 − b_k²))`,

`s_± = √(1 − b_{k±}²)` the genuine radicals.  Each `s·s` collapses to its radicand
by `sqrtFrom_sq_equiv`; the radicand difference is the closed form `bdyOneMinusSq_diff`.
This relates the two radicals' squares (the radical-leg input). -/
theorem radSq_diff_equiv (n : Nat) (hn : 0 < n) (k : Nat)
    (hk0 : 0 < k) (hkn : k < n) (hk1n : k + 1 < n) :
    CReal.Equiv
      (CReal.add
        (CReal.mul (bdyRadical n hn (k + 1)) (bdyRadical n hn (k + 1)))
        (CReal.neg (CReal.mul (bdyRadical n hn k) (bdyRadical n hn k))))
      (CReal.add
        (CReal.ofQ' (bdyOneMinusSq n (k + 1) hn (Nat.succ_pos k) hk1n))
        (CReal.neg (CReal.ofQ' (bdyOneMinusSq n k hn hk0 hkn)))) := by
  -- the two squares collapse to their radicands.
  have hsq1 :
      CReal.Equiv
        (CReal.mul (bdyRadical n hn (k + 1)) (bdyRadical n hn (k + 1)))
        (CReal.ofQ' (bdyOneMinusSq n (k + 1) hn (Nat.succ_pos k) hk1n)) := by
    rw [bdyRadical_interior n hn (k + 1) (Nat.succ_pos k) hk1n]
    exact CReal.sqrtFrom_sq_equiv (bdyOneMinusSq n (k + 1) hn (Nat.succ_pos k) hk1n)
      (SemicircleIntegral.nodeLB n hn) (bdyOneMinusSq_pos hn (Nat.succ_pos k) hk1n)
      (SemicircleIntegral.nodeLB_pos hn) (bdyLB_sq_le hn (Nat.succ_pos k) hk1n)
  have hsq2 :
      CReal.Equiv
        (CReal.mul (bdyRadical n hn k) (bdyRadical n hn k))
        (CReal.ofQ' (bdyOneMinusSq n k hn hk0 hkn)) := by
    rw [bdyRadical_interior n hn k hk0 hkn]
    exact CReal.sqrtFrom_sq_equiv (bdyOneMinusSq n k hn hk0 hkn)
      (SemicircleIntegral.nodeLB n hn) (bdyOneMinusSq_pos hn hk0 hkn)
      (SemicircleIntegral.nodeLB_pos hn) (bdyLB_sq_le hn hk0 hkn)
  -- add the two equivalences (the second under negation) by the Equiv congruence.
  exact addNeg_Equiv_congr hsq1 hsq2

end YMGap.Continuum.ChebOrthoRemainder

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `add_right_comm_eqv` / `pdiff_collect` — the additive abelian-group regrouping
    helpers (the eight-term collection at the heart of the split).
  * **`pdiff_abstract`** — the EXACT abstract `Q'` product-difference identity
    `a·c + (−(b·d)) ≈ ½·((a+b)·(c+(−d))) + ½·((a+(−b))·(c+d))`, pure rational `calc`.
  * `half_factor` — `½·u + (−(½·v)) ≈ ½·(u + (−v))` (combining the two halves of
    the real increment).
  * `splitCReal` / **`pdiff_split_approx`** / **`gIncr_pdiff_split`** — the genuine
    real-boundary increment `gIncrR e he n hn k` equals its sum·difference
    separation `½·(½·(s_+ + s_-)·(B_+ − B_-) + ½·(s_+ − s_-)·(B_+ + B_-))`, proved
    at the approximation level and lifted to a `CReal` `Equiv`.  This isolates the
    smooth-bracket leg (no radical singularity) from the radical leg.
  * `int_sq_step_diff` / **`bdyNum_diff`** — the EXACT closed-form difference of the
    two cell radicands' Int numerators `bdyNum n (k+1) − bdyNum n k = −(4·(2k+1−n))`
    (the difference-of-squares `b_k² − b_{k+1}² = −4·x_k·δ` cleared of `n²`).
  * **`bdyOneMinusSq_diff`** — the radicand difference as a `Q'` identity
    `(1 − b_{k+1}²) + (−(1 − b_k²)) ≈ mkPos (−(4·(2k+1−n))) n²` for an interior pair.
  * `add_shuffle` / `addNeg_Equiv_congr` / `bdyRadical_interior` — the additive
    `Equiv` congruence and the interior-radical unfolding helpers.
  * **`radSq_diff_equiv`** — the `CReal` difference-of-squares of the two genuine
    cell radicals `s_+·s_+ + (−(s_-·s_-)) ≈ ofQ'(1 − b_{k+1}²) + (−ofQ'(1 − b_k²))`
    (interior pair), via `sqrtFrom_sq_equiv` on each leg.

**NAMED-open (the honest residual — the SECOND-ORDER remainder).**
  * `ChebOrthoMidpointCore.CorrectedPerCellBound e he` — the FULL per-cell estimate
    `|cellAdjR e he (N+1) k| ≤ cRate e (N+1) k` against the corrected rate.  The
    product-difference split (`gIncr_pdiff_split`) separates the increment into its
    two finite-difference legs; the proved leading cancellation
    (`ChebOrthoCancel.leading_cancellation`) removes the `O(h)` part EXACTLY; the
    radical-leg radicand difference is the closed form `bdyOneMinusSq_diff`
    /`radSq_diff_equiv`.  The SINGLE remaining genuine content is the constructive
    bound on the SECOND-ORDER centered-difference REMAINDER of each leg (the bracket
    Taylor remainder, scale `Le e`, and the √-Hölder modulus of the radical leg,
    `radDiff_holder`), interior (`C(e)·h^{3/2}/s_k^p`) + boundary (`s_± ≤ √(2δ)`,
    `bdyRadical_leRat`) split balanced at `δ ≈ √h` to the corrected rate.  Recorded
    precisely, not faked.

**Path to closure.**  Once `CorrectedPerCellBound e he` holds for every even
`e ≥ 2`, `ChebOrthoMidpointCore.realPerCellBudget_of_correctedBound` +
`ChebOrthoMidpoint.budgetExists_of_realPerCell` close `BudgetExists e`, hence (via
the proved `convergesTo_czero_of_bound`) `OrthEvenZeroLimit e` and the full π-free
off-diagonal orthogonality `∫U_e√ = 0` for all `e ≥ 1`.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoRemainder.add_right_comm_eqv
#print axioms YMGap.Continuum.ChebOrthoRemainder.pdiff_collect
#print axioms YMGap.Continuum.ChebOrthoRemainder.pdiff_abstract
#print axioms YMGap.Continuum.ChebOrthoRemainder.half_factor
#print axioms YMGap.Continuum.ChebOrthoRemainder.pdiff_split_approx
#print axioms YMGap.Continuum.ChebOrthoRemainder.gIncr_pdiff_split
#print axioms YMGap.Continuum.ChebOrthoRemainder.int_sq_step_diff
#print axioms YMGap.Continuum.ChebOrthoRemainder.bdyNum_diff
#print axioms YMGap.Continuum.ChebOrthoRemainder.bdyOneMinusSq_diff
#print axioms YMGap.Continuum.ChebOrthoRemainder.add_shuffle
#print axioms YMGap.Continuum.ChebOrthoRemainder.addNeg_Equiv_congr
#print axioms YMGap.Continuum.ChebOrthoRemainder.bdyRadical_interior
#print axioms YMGap.Continuum.ChebOrthoRemainder.radSq_diff_equiv
