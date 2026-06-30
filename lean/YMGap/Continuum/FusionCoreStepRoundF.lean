/-
Track A / R2 — Round F of the fusion box log-concavity node: the ANDRÉIEF / CAUCHY–BINET
HALF-SUM IDENTITY, proved in full, closing the COMMON-RANGE total positivity (A2's
analytic core), plus an HONEST routing of the remaining open content to the single
sharpest residual (A3 = the `r`-aggregation / sum-of-log-concave wall).

# What this module adds (read first — load-bearing honesty)

`FusionCoreStepRoundE` proved the per-summand Cauchy–Binet positivity
(`coeffMinorProd_nonneg`: a product of two Hankel `2×2` minors is `≥ 0`) and the Hankel
rectangle log-concavity (`coeffW_rect`), and named the remaining open content of A2
(`LagCorrTP2`) as the Andréief half-sum identity plus the `N`-truncation boundary defect.
Round F supplies that half-sum identity SYMBOLICALLY and closes the common-range total
positivity it implies.

ROUND-F DELIVERABLE 1 (the generic Plücker / Andréief identity — PROVED, axiom-clean).
  * `plucker8` — the 8-variable bilinear-minor identity
        (α γ)(β'δ') − (α δ)(β'γ')  +  (α'γ')(β δ) − (α'δ')(β γ)
          =  (α β' − α' β) · (γ δ' − γ' δ).
    This is the per-pair antisymmetrized content of the Andréief/Cauchy–Binet expansion:
    the symmetrized `(a,b)+(b,a)` summand of the `2×2` line-correlation determinant equals
    the PRODUCT of the two row-minors.  Pure `Q'` distributivity + four `mul_swap4`
    monomial regroupings; no positivity, no new axiom.

ROUND-F DELIVERABLE 2 (the half-sum determinant identity and its nonnegativity — PROVED).
  * `lagCorrCR` — the COMMON-RANGE lag-correlation `Σ_{r<n} c_{p+r} c_{q+r}` (a single
    shared cutoff `n` for all strand arguments; `lagCorr w N p q = lagCorrCR w (N+1−max p q)
    p q` by `lagCorr_eq_cr`).
  * `Mdet` — the `2×2` line-correlation determinant
        lagCorrCR(p,q)·lagCorrCR(p',q') − lagCorrCR(p,q')·lagCorrCR(p',q).
  * `Mdet_double_eq` — THE HALF-SUM IDENTITY: `Mdet + Mdet ≃ Σ_a Σ_b minorProd(a,b)`,
    where `minorProd(a,b) = pminor(p,p',a,b)·pminor(q,q',a,b)` is the product of the two
    Hankel row-minors.  (`fsum_mul_fsum` to open the products into a double sum, `fsum_swap`
    to symmetrize `a↔b`, and `plucker8` per summand.)
  * `minorProd_nonneg` — every summand is `≥ 0` (two `≤ 0` Hankel minors for `a ≤ b`, two
    `≥ 0` for `b ≤ a`), via `coeffMinor_nonpos` + the antisymmetry `pminor_antisymm`.
  * `Mdet_nonneg` — hence `Mdet ≥ 0` (the doubled sum is `≥ 0`; cancel the positive `2`).

ROUND-F DELIVERABLE 3 (the closed common-range total positivity — PROVED).
  * `lagCorrTP2_common` — `p ≤ p', q ≤ q' ⟹ lagCorrCR(p,q')·lagCorrCR(p',q) ≤
    lagCorrCR(p,q)·lagCorrCR(p',q')`.  The genuine "common-range truncated lag-correlation
    of the theta weight is totally positive of order 2", proved UNCONDITIONALLY (the
    Andréief half-sum closes it; no `LagCorrTP2`, no `QuadGershgorinClosure` hypothesis).

# HONESTY — what is NOT closed (the dependency correction kept sharp)

`StrandReduction`'s two fields are A1 (`reindex`, the strand bijection
`boxSum ≃ lineSum lagCorr`) and A3 (`lineSumLogConcave`, the antidiagonal line-sum
log-concavity); A2 (`LagCorrTP2`) is a stepping-stone that SEEDS A3, not a field on the
critical path.  Round F closes the COMMON-RANGE half-sum core (`lagCorrTP2_common`) — the
genuine new analytic result the scout's tool targets — but this does NOT inhabit
`StrandReduction`, and hence does NOT close `S1Dominance` for all `N`, because:

  * A2 with the REAL per-pair ranges (`lagCorr`, range `N+1−max(p,q)`, shortest for
    `(p',q')`) differs from the common-range `Mdet` by the boundary surplus of the three
    longer sums.  That boundary defect — absorbed by the factor-4 reserve
    `coeffW_superLogConcave` — is the residual of full `LagCorrTP2` (NAMED open here).
  * A3 is the GENUINE WALL.  A sum `Σ_r h_r` of per-shift log-concave autoconvolutions is
    NOT log-concave in general (`bracket_can_be_negative`; the rank-1 `f=(1,0,1)`,
    `L=(1,0,2,0,1)` slice of `RoundE`).  The half-sum gives TP₂ of the kernel but TP₂ does
    NOT imply PF₂ of its antidiagonal line-sums.  So A3 = `lineSumLogConcave` =
    `QuadGershgorinClosure` (the heat-kernel local-CLT) is the single sharpest residual,
    now with seed `coeffW_rect` and the `r`-aggregation as the isolated open content.

This is NOT a 4D Yang–Mills mass gap; it is the symbolic Andréief half-sum identity, the
closed common-range total positivity of the theta weight, and the honest routing of the
remaining open content to the `r`-aggregation wall (A3).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`fsum`/`coeffMinor` lemmas, `mul_swap4`
regroupings, finite `fsum` algebra (`fsum_mul_fsum`, `fsum_swap`, `fsum_add`, `fsum_neg`,
`fsum_nonneg`), and `omega` on index identities.  Every load-bearing declaration is gated
with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No `Classical.*`,
no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.FusionCoreStepRoundE

namespace YMGap.Continuum.FusionCoreStepRoundF

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionCoreStepRoundE

/-! ## 0. Small `Q'` helpers -/

/-- `0 ≤ -x` from `x ≤ 0`. -/
theorem neg_nonneg_of_nonpos {x : Q'} (hx : x ≤ (0 : Q')) : (0 : Q') ≤ -x :=
  Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hx) (Q'.le_of_eqv (q_zero_add_eqv (-x)))

/-- `(-a)·(-b) ≃ a·b`. -/
theorem neg_mul_neg_eqv (a b : Q') : ((-a) * (-b)).eqv (a * b) :=
  Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv a (-b))
    (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv a b))
      (Q'.neg_neg_eqv (a * b)))

/-! ## 1. The generic Plücker / Andréief minor identity -/

/-- **`plucker8` — the bilinear `2×2`-minor (Plücker) identity over `Q'`.**

    ((α·γ)·(β'·δ') − (α·δ)·(β'·γ'))  +  ((α'·γ')·(β·δ) − (α'·δ')·(β·γ))
      ≃  (α·β' − α'·β) · (γ·δ' − γ'·δ).

The left side is the symmetrized `(a,b)+(b,a)` summand of a `2×2` line-correlation
determinant; the right side is the product of the two row-minors.  Proof: expand the RHS
by distributivity into four signed monomials, expand the LHS, and match each monomial via
`mul_swap4` (four-factor regrouping) + commutativity.  Pure `Q'` algebra. -/
theorem plucker8 (α α' β β' γ γ' δ δ' : Q') :
    (((α * γ) * (β' * δ') + -((α * δ) * (β' * γ')))
      + ((α' * γ') * (β * δ) + -((α' * δ') * (β * γ)))).eqv
      ((α * β' + -(α' * β)) * (γ * δ' + -(γ' * δ))) := by
  -- RHS ≃ E := (m1 + m2) + (m3 + m4) with the four canonical signed monomials.
  have hRHS : ((α * β' + -(α' * β)) * (γ * δ' + -(γ' * δ))).eqv
      (((α * β') * (γ * δ') + -((α * β') * (γ' * δ)))
        + (-((α' * β) * (γ * δ')) + (α' * β) * (γ' * δ))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (α * β') (-(α' * β)) (γ * δ' + -(γ' * δ))) ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · -- (α·β')·(γδ' + -(γ'δ)) ≃ m1 + m2
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (α * β') (γ * δ') (-(γ' * δ))) ?_
      exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv (α * β') (γ' * δ))
    · -- (-(α'·β))·(γδ' + -(γ'δ)) ≃ m3 + m4
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (-(α' * β)) (γ * δ') (-(γ' * δ))) ?_
      refine Q'.add_eqv_congr' ?_ ?_
      · exact Q'.neg_mul_eqv (α' * β) (γ * δ')
      · exact neg_mul_neg_eqv (α' * β) (γ' * δ)
  -- LHS monomial matches (L1≃m1, L2≃m2, L3≃m4, L4≃m3).
  have hL1 : ((α * γ) * (β' * δ')).eqv ((α * β') * (γ * δ')) := mul_swap4 α γ β' δ'
  have hL2 : (-((α * δ) * (β' * γ'))).eqv (-((α * β') * (γ' * δ))) := by
    refine Q'.neg_eqv_congr _ _ ?_
    refine Q'.eqv_trans _ _ _ (mul_swap4 α δ β' γ') ?_
    exact Q'.mul_eqv_congr_left (α * β') _ _ (Q'.mul_comm_eqv δ γ')
  have hL3 : ((α' * γ') * (β * δ)).eqv ((α' * β) * (γ' * δ)) := mul_swap4 α' γ' β δ
  have hL4 : (-((α' * δ') * (β * γ))).eqv (-((α' * β) * (γ * δ'))) := by
    refine Q'.neg_eqv_congr _ _ ?_
    refine Q'.eqv_trans _ _ _ (mul_swap4 α' δ' β γ) ?_
    exact Q'.mul_eqv_congr_left (α' * β) _ _ (Q'.mul_comm_eqv δ' γ)
  -- LHS ≃ E (the second group needs an a↔b commute, L3+L4 ≃ m4+m3 ≃ m3+m4).
  have hLHS : (((α * γ) * (β' * δ') + -((α * δ) * (β' * γ')))
      + ((α' * γ') * (β * δ) + -((α' * δ') * (β * γ)))).eqv
      (((α * β') * (γ * δ') + -((α * β') * (γ' * δ)))
        + (-((α' * β) * (γ * δ')) + (α' * β) * (γ' * δ))) := by
    refine Q'.add_eqv_congr' (Q'.add_eqv_congr' hL1 hL2) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hL3 hL4) ?_
    exact Q'.add_comm_eqv ((α' * β) * (γ' * δ)) (-((α' * β) * (γ * δ')))
  exact Q'.eqv_trans _ _ _ hLHS (Q'.eqv_symm hRHS)

/-! ## 2. The common-range lag-correlation and its `2×2` determinant -/

/-- The COMMON-RANGE lag-correlation `Σ_{r<n} c_{p+r}·c_{q+r}` (a single cutoff `n`). -/
def lagCorrCR (w : Q') (n p q : Nat) : Q' :=
  fsum (fun r => coeffW w (p + r) * coeffW w (q + r)) n

/-- The real `lagCorr` (RoundD, range `N+1−max p q`) is the common-range correlation at
the pair-dependent cutoff `N+1−max p q`.  (Definitional bridge.) -/
theorem lagCorr_eq_cr (w : Q') (N p q : Nat) :
    lagCorr w N p q = lagCorrCR w (N + 1 - Nat.max p q) p q := rfl

/-- The single Hankel row-minor `pminor(p,p',a,b) = c_{p+a}c_{p'+b} − c_{p+b}c_{p'+a}`. -/
def pminor (w : Q') (p p' a b : Nat) : Q' :=
  coeffW w (p + a) * coeffW w (p' + b) + -(coeffW w (p + b) * coeffW w (p' + a))

/-- The `2×2` line-correlation determinant of the common-range lag-correlation. -/
def Mdet (w : Q') (n p q p' q' : Nat) : Q' :=
  lagCorrCR w n p q * lagCorrCR w n p' q' + -(lagCorrCR w n p q' * lagCorrCR w n p' q)

/-- The symmetrized determinant summand (the `(a,b)` term of `Mdet` opened as a double
sum). -/
def term2 (w : Q') (p q p' q' a b : Nat) : Q' :=
  (coeffW w (p + a) * coeffW w (q + a)) * (coeffW w (p' + b) * coeffW w (q' + b))
    + -((coeffW w (p + a) * coeffW w (q' + a)) * (coeffW w (p' + b) * coeffW w (q + b)))

/-- The product of the two row-minors — the per-pair summand of the half-sum. -/
def minorProd (w : Q') (p q p' q' a b : Nat) : Q' :=
  pminor w p p' a b * pminor w q q' a b

/-! ### 2a. Antisymmetry of the row-minor and per-summand nonnegativity -/

/-- **`pminor_antisymm`** — `pminor(p,p',a,b) ≃ −pminor(p,p',b,a)` (the Hankel minor is
antisymmetric in its two column indices). -/
theorem pminor_antisymm (w : Q') (p p' a b : Nat) :
    (pminor w p p' a b).eqv (-(pminor w p p' b a)) := by
  unfold pminor
  -- pminor a b = P + -Q,  pminor b a = Q + -P  with  P = c_{p+a}c_{p'+b}, Q = c_{p+b}c_{p'+a}
  -- so -(pminor b a) = -(Q + -P) ≃ -Q + P ≃ P + -Q.
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.neg_add_eqv (coeffW w (p + b) * coeffW w (p' + a))
      (-(coeffW w (p + a) * coeffW w (p' + b)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv (coeffW w (p + a) * coeffW w (p' + b)))) ?_
  exact Q'.add_comm_eqv _ _

/-- **`pminor_eq_coeffMinor`** — for `p ≤ p'` and `a ≤ b`, the row-minor equals the
`RoundE` Hankel minor `coeffMinor w p (p'−p) a (b−a)`. -/
theorem pminor_eq_coeffMinor {w : Q'} {p p' a b : Nat} (hpp' : p ≤ p') (hab : a ≤ b) :
    pminor w p p' a b = coeffMinor w p (p' - p) a (b - a) := by
  unfold pminor coeffMinor
  rw [show p' + b = p + (p' - p) + (a + (b - a)) by omega,
      show p + b = p + (a + (b - a)) by omega,
      show p' + a = p + (p' - p) + a by omega]

/-- **`pminor_nonpos`** — for `p ≤ p'` and `a ≤ b`, the row-minor is `≤ 0`. -/
theorem pminor_nonpos {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) {p p' a b : Nat} (hpp' : p ≤ p') (hab : a ≤ b) :
    pminor w p p' a b ≤ (0 : Q') := by
  rw [pminor_eq_coeffMinor hpp' hab]
  exact coeffMinor_nonpos hw0 hw1 hwpos p (p' - p) a (b - a)

/-- **`pminor_nonneg`** — for `p ≤ p'` and `b ≤ a`, the row-minor is `≥ 0` (antisymmetry
flips the `a ≤ b` sign). -/
theorem pminor_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) {p p' a b : Nat} (hpp' : p ≤ p') (hba : b ≤ a) :
    (0 : Q') ≤ pminor w p p' a b := by
  have hnp : pminor w p p' b a ≤ (0 : Q') := pminor_nonpos hw0 hw1 hwpos hpp' hba
  exact Q'.le_trans' _ _ _ (neg_nonneg_of_nonpos hnp)
    (Q'.le_of_eqv (Q'.eqv_symm (pminor_antisymm w p p' a b)))

/-- **`minorProd_nonneg`** — every half-sum summand is `≥ 0`.  Both row-minors are `≤ 0`
when `a ≤ b` (product of two nonpositives) and both `≥ 0` when `b ≤ a`. -/
theorem minorProd_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) {p q p' q' : Nat} (hpp' : p ≤ p') (hqq' : q ≤ q') (a b : Nat) :
    (0 : Q') ≤ minorProd w p q p' q' a b := by
  unfold minorProd
  rcases Nat.le_total a b with hab | hba
  · exact q_mul_nonpos_nonpos (pminor_nonpos hw0 hw1 hwpos hpp' hab)
      (pminor_nonpos hw0 hw1 hwpos hqq' hab)
  · exact Q'.mul_nonneg _ _ (pminor_nonneg hw0 hw1 hwpos hpp' hba)
      (pminor_nonneg hw0 hw1 hwpos hqq' hba)

/-! ### 2b. Depth-2 `fsum` add / neg combinators -/

/-- `Σ_a Σ_b F + Σ_a Σ_b G ≃ Σ_a Σ_b (F + G)`. -/
theorem q2_add (F G : Nat → Nat → Q') (n : Nat) :
    (fsum (fun a => fsum (F a) n) n + fsum (fun a => fsum (G a) n) n).eqv
      (fsum (fun a => fsum (fun b => F a b + G a b) n) n) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (fsum_add (fun a => fsum (F a) n) (fun a => fsum (G a) n) n)) ?_
  exact fsum_eqv_congr _ _ (fun a => Q'.eqv_symm (fsum_add (F a) (G a) n)) n

/-- `−(Σ_a Σ_b F) ≃ Σ_a Σ_b (−F)`. -/
theorem q2_neg (F : Nat → Nat → Q') (n : Nat) :
    (-(fsum (fun a => fsum (F a) n) n)).eqv
      (fsum (fun a => fsum (fun b => -(F a b)) n) n) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (fsum_neg (fun a => fsum (F a) n) n)) ?_
  exact fsum_eqv_congr _ _ (fun a => Q'.eqv_symm (fsum_neg (F a) n)) n

/-! ### 2c. The half-sum identity -/

/-- The pointwise Plücker identity in `coeffW` form: the symmetrized determinant summand
`term2(a,b) + term2(b,a)` equals the product of row-minors `minorProd(a,b)`. -/
theorem term2_swap_eq_minorProd (w : Q') (p q p' q' a b : Nat) :
    (term2 w p q p' q' a b + term2 w p q p' q' b a).eqv (minorProd w p q p' q' a b) := by
  unfold term2 minorProd pminor
  exact plucker8 (coeffW w (p + a)) (coeffW w (p + b)) (coeffW w (p' + a))
    (coeffW w (p' + b)) (coeffW w (q + a)) (coeffW w (q + b)) (coeffW w (q' + a))
    (coeffW w (q' + b))

/-- **`Mdet_eq_termSum`** — the common-range determinant is the double sum of `term2`.
`fsum_mul_fsum` opens each product of column sums into a double sum; the two double sums
combine into one. -/
theorem Mdet_eq_termSum (w : Q') (n p q p' q' : Nat) :
    (Mdet w n p q p' q').eqv
      (fsum (fun a => fsum (fun b => term2 w p q p' q' a b) n) n) := by
  unfold Mdet
  have hAB : (lagCorrCR w n p q * lagCorrCR w n p' q').eqv
      (fsum (fun a => fsum (fun b =>
        (coeffW w (p + a) * coeffW w (q + a)) * (coeffW w (p' + b) * coeffW w (q' + b)))
        n) n) :=
    fsum_mul_fsum (fun a => coeffW w (p + a) * coeffW w (q + a))
      (fun b => coeffW w (p' + b) * coeffW w (q' + b)) n n
  have hCD : (lagCorrCR w n p q' * lagCorrCR w n p' q).eqv
      (fsum (fun a => fsum (fun b =>
        (coeffW w (p + a) * coeffW w (q' + a)) * (coeffW w (p' + b) * coeffW w (q + b)))
        n) n) :=
    fsum_mul_fsum (fun a => coeffW w (p + a) * coeffW w (q' + a))
      (fun b => coeffW w (p' + b) * coeffW w (q + b)) n n
  -- Mdet ≃ ΣΣ kPlus + -(ΣΣ kMinus) ≃ ΣΣ kPlus + ΣΣ (-kMinus) ≃ ΣΣ (kPlus + -kMinus) = ΣΣ term2
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hAB (Q'.neg_eqv_congr _ _ hCD)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _
    (q2_neg (fun a b =>
      (coeffW w (p + a) * coeffW w (q' + a)) * (coeffW w (p' + b) * coeffW w (q + b))) n)) ?_
  exact q2_add
    (fun a b => (coeffW w (p + a) * coeffW w (q + a)) * (coeffW w (p' + b) * coeffW w (q' + b)))
    (fun a b => -((coeffW w (p + a) * coeffW w (q' + a)) * (coeffW w (p' + b) * coeffW w (q + b))))
    n

/-- **`Mdet_double_eq` — THE ANDRÉIEF HALF-SUM IDENTITY.**  Twice the common-range
determinant equals the double sum of the row-minor products:
`Mdet + Mdet ≃ Σ_a Σ_b minorProd(a,b)`.  (`Mdet ≃ Σ term2(a,b) ≃ Σ term2(b,a)` by the
`a↔b` swap; add and apply `term2_swap_eq_minorProd` per summand.) -/
theorem Mdet_double_eq (w : Q') (n p q p' q' : Nat) :
    (Mdet w n p q p' q' + Mdet w n p q p' q').eqv
      (fsum (fun a => fsum (fun b => minorProd w p q p' q' a b) n) n) := by
  have hS : (Mdet w n p q p' q').eqv
      (fsum (fun a => fsum (fun b => term2 w p q p' q' a b) n) n) :=
    Mdet_eq_termSum w n p q p' q'
  -- swapped form: Mdet ≃ ΣΣ term2(b,a)
  have hSwap : (fsum (fun a => fsum (fun b => term2 w p q p' q' a b) n) n).eqv
      (fsum (fun a => fsum (fun b => term2 w p q p' q' b a) n) n) :=
    fsum_swap (fun a b => term2 w p q p' q' a b) n n
  have hS' : (Mdet w n p q p' q').eqv
      (fsum (fun a => fsum (fun b => term2 w p q p' q' b a) n) n) :=
    Q'.eqv_trans _ _ _ hS hSwap
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hS hS') ?_
  refine Q'.eqv_trans _ _ _
    (q2_add (fun a b => term2 w p q p' q' a b) (fun a b => term2 w p q p' q' b a) n) ?_
  exact fsum_eqv_congr _ _
    (fun a => fsum_eqv_congr _ _ (fun b => term2_swap_eq_minorProd w p q p' q' a b) n) n

/-! ## 3. Nonnegativity of the determinant and the closed common-range TP₂ -/

/-- **`Mdet_nonneg`** — the common-range `2×2` line-correlation determinant is `≥ 0`.
The doubled determinant is `Σ_a Σ_b minorProd ≥ 0` (`fsum_nonneg` twice, `minorProd_nonneg`
per summand); cancel the positive factor `2`. -/
theorem Mdet_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) {p q p' q' : Nat} (hpp' : p ≤ p') (hqq' : q ≤ q') (n : Nat) :
    (0 : Q') ≤ Mdet w n p q p' q' := by
  -- doubled determinant ≥ 0
  have hsum : (0 : Q') ≤ fsum (fun a => fsum (fun b => minorProd w p q p' q' a b) n) n :=
    fsum_nonneg (fun a =>
      fsum_nonneg (fun b => minorProd_nonneg hw0 hw1 hwpos hpp' hqq' a b) n) n
  have hdouble : (0 : Q') ≤ Mdet w n p q p' q' + Mdet w n p q p' q' :=
    Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv (Mdet_double_eq w n p q p' q'))
  -- 0 ≤ 2 · Mdet, then cancel the positive 2
  have h2pos : (0 : Q') < Q'.ofNat 2 := Q'.ofNat_succ_pos 1
  have hmul : (0 : Q') ≤ Q'.ofNat 2 * Mdet w n p q p' q' :=
    Q'.le_trans' _ _ _ hdouble (Q'.ge_of_eqv (ofNat_two_mul_eqv (Mdet w n p q p' q')))
  have hmul0 : Q'.ofNat 2 * (0 : Q') ≤ Q'.ofNat 2 * Mdet w n p q p' q' :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (q_mul_zero (Q'.ofNat 2))) hmul
  exact le_of_mul_le_mul_left_pos h2pos hmul0

/-- **`lagCorrTP2_common` — THE CLOSED COMMON-RANGE TOTAL POSITIVITY (A2's analytic core).**
For `0 < w ≤ 1` and any shared cutoff `n`,

    p ≤ p',  q ≤ q'   ⟹   lagCorrCR(p,q')·lagCorrCR(p',q) ≤ lagCorrCR(p,q)·lagCorrCR(p',q').

The truncated lag-correlation of the theta weight at a single common range is totally
positive of order 2 — proved UNCONDITIONALLY via the Andréief half-sum identity
(`Mdet_nonneg`), no `LagCorrTP2`/`QuadGershgorinClosure` hypothesis. -/
theorem lagCorrTP2_common {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) {p q p' q' : Nat} (hpp' : p ≤ p') (hqq' : q ≤ q') (n : Nat) :
    lagCorrCR w n p q' * lagCorrCR w n p' q ≤ lagCorrCR w n p q * lagCorrCR w n p' q' :=
  Q'.le_of_sub_nonneg (Mdet_nonneg hw0 hw1 hwpos hpp' hqq' n)

/-! ## 4. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `plucker8` — the generic bilinear `2×2`-minor (Plücker/Andréief) identity over `Q'`.
  * `pminor_antisymm`, `pminor_eq_coeffMinor`, `pminor_nonpos`, `pminor_nonneg`,
    `minorProd_nonneg` — the row-minor algebra and per-summand sign (from `coeffMinor`).
  * `Mdet_eq_termSum`, `Mdet_double_eq` — the half-sum identity `Mdet + Mdet ≃
    Σ_a Σ_b minorProd(a,b)`.
  * `Mdet_nonneg` — the common-range `2×2` line-correlation determinant is `≥ 0`.
  * `lagCorrTP2_common` — the CLOSED common-range total positivity of the theta weight
    (A2's analytic core), proved unconditionally.
  * `lagCorr_eq_cr` — the definitional bridge from the real per-pair `lagCorr` to
    `lagCorrCR`.

NAMED OPEN (carried; NOT inhabited here — the honest dependency correction):
  * `LagCorrTP2 w` (A2, full per-pair ranges) — equals `lagCorrTP2_common` PLUS the
    boundary reconciliation of the four different per-pair cutoffs `N+1−max(·,·)` (the
    surplus terms of the three longer sums), absorbed by `coeffW_superLogConcave`.  A2 is a
    stepping-stone, NOT a field of `StrandReduction`.
  * `StrandReduction w` = A1 (`reindex`) + A3 (`lineSumLogConcave`).  A3 is the GENUINE
    WALL: `Σ_r h_r` of per-shift log-concave autoconvolutions is not log-concave in general
    (`bracket_can_be_negative`); TP₂ of the kernel (proved here for the common range) does
    NOT imply PF₂ of its antidiagonal line-sums.  A3 = `QuadGershgorinClosure` (the
    heat-kernel local-CLT), seed `coeffW_rect`, with the `r`-aggregation isolated as the
    single sharpest residual.

HONEST VERDICT.  Round F proves the Andréief/Cauchy–Binet half-sum identity and closes the
COMMON-RANGE total positivity of the theta weight — the genuine new analytic result A2's
core needed — but this does NOT inhabit `StrandReduction` and does NOT close `S1Dominance`
for all `N`: the per-pair boundary defect (full A2) and, decisively, the `r`-aggregation /
sum-of-log-concave wall (A3 = `QuadGershgorinClosure`) remain the open content.  This is a
structural advance on one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass
gap. -/

end YMGap.Continuum.FusionCoreStepRoundF

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundF.plucker8
#print axioms YMGap.Continuum.FusionCoreStepRoundF.pminor_antisymm
#print axioms YMGap.Continuum.FusionCoreStepRoundF.pminor_eq_coeffMinor
#print axioms YMGap.Continuum.FusionCoreStepRoundF.pminor_nonpos
#print axioms YMGap.Continuum.FusionCoreStepRoundF.pminor_nonneg
#print axioms YMGap.Continuum.FusionCoreStepRoundF.minorProd_nonneg
#print axioms YMGap.Continuum.FusionCoreStepRoundF.term2_swap_eq_minorProd
#print axioms YMGap.Continuum.FusionCoreStepRoundF.Mdet_eq_termSum
#print axioms YMGap.Continuum.FusionCoreStepRoundF.Mdet_double_eq
#print axioms YMGap.Continuum.FusionCoreStepRoundF.Mdet_nonneg
#print axioms YMGap.Continuum.FusionCoreStepRoundF.lagCorrTP2_common
