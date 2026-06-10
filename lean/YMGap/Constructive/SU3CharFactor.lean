/-
U.6 A1.2 — the `Q'` rendering of the SU(3) irrep data and the *prefactor
half* of the factorized character-tail majorant, plus the cross-term
factor bound `e^{−x} ≤ 1`.

The character tail `Z_t = Σ_{(p,q)≠(0,0)} dim(p,q)²·e^{−t·C₂(p,q)}` is
bounded termwise by the factorized majorant `a(p,q) ≤ g(p)·g(q)` with
`g(x) = (x+1)⁴·e^{−t·f(x)}`.  Writing the heat-kernel exponent through the
*exact* Casimir split `C₂(p,q) = f(p) + f(q) + pq/3`
(`threeCasimir_split_eq`, the equality strengthening of
`RepTheory.SU3.casimir_split_le`), the term factorizes as

    a(p,q) = dim(p,q)²·e^{−t·f(p)}·e^{−t·f(q)}·e^{−t·(pq/3)}
           ≤ [(p+1)⁴(q+1)⁴]·e^{−t·f(p)}·e^{−t·f(q)}·1
           = g(p)·g(q),

using `dimSq_le` (prefactor) and `e^{−t·(pq/3)} ≤ 1` (cross term).

This module delivers the two halves that need no new substrate:

  * `dimSqQ_le` — the *prefactor half*, `dim(p,q)² ≤ gPrefactor p · q`
    lifted to `Q'` (from `RepTheory.SU3.dimSq_le`), in `leRat`-ready form.
  * `expNeg_le_one` — the *cross-term factor bound* `leRat (e^{−x}) 1`
    for `x ≥ 0`, derived from the U.5 soundness `e^{−x} ≤ 1/(1+x)` and
    `1/(1+x) ≤ 1` (`oneOver1p` antitone, `= 1` at `0`).  (This is the
    `expNeg_le_one_of_nonneg` item flagged "remaining" in `ExpNeg.lean`'s
    header; it closes here.)

The remaining *exponent half* — assembling the three exponential factors
via the addition law `expNeg_add_equiv` — needs one further substrate
lemma not yet present: that `expNeg` respects `.eqv` of its (rational)
argument (`t·C₂` equals `t·f(p)+t·f(q)+t·(pq/3)` only up to `.eqv`, since
`Q'` addition is not definitional).  That `expNeg_eqv_congr` is the single
next step to the full per-term factorization `charTerm2D_le`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

`[propext]`, plus `Quot.sound` where `omega`/`Nat`/`Int` enter.  No
`Classical.*`, no `sorryAx`.
-/

import YMGap.RepTheory.SU3
import YMGap.Constructive.Soundness
import YMGap.Constructive.CRealMulLe
import YMGap.Constructive.ExpNegCongr

namespace YMGap.Constructive.SU3CharFactor

open YMGap.Constructive
open YMGap.RepTheory

/-! ## `Q'` rendering of the SU(3) irrep data

The Casimir `C₂` and per-index lower bound `f` carry a `/3`; we render
them as `mkPos (·) 3`.  The dimension square and the majorant prefactor
`(x+1)⁴` are integers, rendered via `ofNat`. -/

/-- `f(x) = (x²+3x)/3` as a `Q'` (`= threeF x / 3`). -/
def fQ (x : Nat) : Q' := Q'.mkPos (SU3.threeF x : Int) 3 (by decide)

/-- `C₂(p,q) = (p²+q²+pq+3p+3q)/3` as a `Q'` (`= threeCasimir p q / 3`). -/
def casimirQ (p q : Nat) : Q' := Q'.mkPos (SU3.threeCasimir p q : Int) 3 (by decide)

/-- The cross term `pq/3` as a `Q'`. -/
def crossQ (p q : Nat) : Q' := Q'.mkPos ((p * q : Nat) : Int) 3 (by decide)

/-- The majorant prefactor `(x+1)⁴` as a `Q'`. -/
def gPrefQ (x : Nat) : Q' := Q'.ofNat (SU3.gPrefactor x)

/-- The per-irrep prefactor `dim(p,q)²` as a `Q'`. -/
def dimSqQ (p q : Nat) : Q' := Q'.ofNat (SU3.dim p q * SU3.dim p q)

/-! ## Nonnegativity (numerators are `Nat` casts) -/

theorem fQ_nonneg (x : Nat) : (0 : Q') ≤ fQ x := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (SU3.threeF x : Int)
  exact Int.natCast_nonneg _

theorem casimirQ_nonneg (p q : Nat) : (0 : Q') ≤ casimirQ p q := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (SU3.threeCasimir p q : Int)
  exact Int.natCast_nonneg _

theorem crossQ_nonneg (p q : Nat) : (0 : Q') ≤ crossQ p q := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ ((p * q : Nat) : Int)
  exact Int.natCast_nonneg _

/-! ## The exact Casimir split (equality form of `casimir_split_le`)

`3·C₂(p,q) = 3·f(p) + 3·f(q) + pq` exactly — the cross term `pq` is the
*equality* defect of the `casimir_split_le` inequality, and is what the
addition-law factorization consumes. -/

theorem threeCasimir_split_eq (p q : Nat) :
    SU3.threeCasimir p q = SU3.threeF p + SU3.threeF q + p * q := by
  show p * p + q * q + p * q + 3 * p + 3 * q
      = (p * p + 3 * p) + (q * q + 3 * q) + p * q
  omega

/-! ## Prefactor half of the factorization

`dim(p,q)² ≤ (p+1)⁴(q+1)⁴`, lifted from the `Nat` fact
`RepTheory.SU3.dimSq_le` to a `Q'` bound on the prefactor.  RHS kept as
`ofNat (gPrefactor p · gPrefactor q)` — already factored at the `Nat`
level — so the lift is a single `ofNat_le_ofNat`. -/

theorem dimSqQ_le (p q : Nat) :
    dimSqQ p q ≤ Q'.ofNat (SU3.gPrefactor p * SU3.gPrefactor q) :=
  CReal.ofNat_le_ofNat (SU3.dimSq_le p q)

/-! ## Cross-term factor bound `e^{−x} ≤ 1`

`expNeg x ≤ 1/(1+x)` (U.5 soundness) and `1/(1+x) ≤ 1/(1+0) = 1` for
`x ≥ 0` (`oneOver1p` antitone). -/

theorem expNeg_le_one (x : Q') (hx : (0 : Q') ≤ x) :
    CReal.leRat (ExpNeg.expNeg x hx) 1 := by
  have h1 : CReal.leRat (ExpNeg.expNeg x hx) (ExpUBInstance.oneOver1p x) :=
    expNeg_le_oneOver1p x hx
  have h2 : ExpUBInstance.oneOver1p x ≤ 1 := by
    have hanti := ExpUBInstance.oneOver1p_antitone 0 x hx
    rwa [ExpUBInstance.oneOver1p_zero] at hanti
  exact CReal.leRat_mono h1 h2

/-! ## Exponent split: `C₂(p,q) = f(p) + f(q) + pq/3` over `Q'`

The three data are all `mkPos (·) 3`; same-denominator addition gives the
`.eqv` split, which `expNeg_eqv_congr` then transports under `expNeg`. -/

/-- Same-denominator-`3` addition: `a/3 + b/3 ≃ (a+b)/3`. -/
theorem mkPos3_add_eqv (a b : Int) :
    (Q'.mkPos a 3 (by decide) + Q'.mkPos b 3 (by decide)).eqv
      (Q'.mkPos (a + b) 3 (by decide)) := by
  show (Q'.mkPos a 3 (by decide) + Q'.mkPos b 3 (by decide)).num
        * ((Q'.mkPos (a + b) 3 (by decide)).den : Int)
     = (Q'.mkPos (a + b) 3 (by decide)).num
        * ((Q'.mkPos a 3 (by decide) + Q'.mkPos b 3 (by decide)).den : Int)
  have hLnum : (Q'.mkPos a 3 (by decide) + Q'.mkPos b 3 (by decide)).num
      = a * 3 + b * 3 := rfl
  have hLden : (Q'.mkPos a 3 (by decide) + Q'.mkPos b 3 (by decide)).den = 9 := rfl
  rw [hLnum, hLden]
  show (a * 3 + b * 3) * ((3 : Nat) : Int) = (a + b) * ((9 : Nat) : Int)
  push_cast
  omega

/-- The exact Casimir split over `Q'`:
`C₂(p,q) ≃ f(p) + (f(q) + pq/3)`. -/
theorem casimirQ_split_eqv (p q : Nat) :
    (casimirQ p q).eqv (fQ p + (fQ q + crossQ p q)) := by
  -- f(q) + pq/3 ≃ (threeF q + pq)/3, then f(p) + that ≃ (threeF p + (threeF q + pq))/3
  have h1 : (fQ q + crossQ p q).eqv
      (Q'.mkPos ((SU3.threeF q : Int) + (p * q : Nat)) 3 (by decide)) :=
    mkPos3_add_eqv (SU3.threeF q : Int) ((p * q : Nat) : Int)
  have h2 : (fQ p + (fQ q + crossQ p q)).eqv
      (fQ p + Q'.mkPos ((SU3.threeF q : Int) + (p * q : Nat)) 3 (by decide)) :=
    Q'.add_eqv_congr_left _ _ _ h1
  have h3 : (fQ p + Q'.mkPos ((SU3.threeF q : Int) + (p * q : Nat)) 3 (by decide)).eqv
      (Q'.mkPos ((SU3.threeF p : Int) + ((SU3.threeF q : Int) + (p * q : Nat))) 3 (by decide)) :=
    mkPos3_add_eqv (SU3.threeF p : Int) ((SU3.threeF q : Int) + (p * q : Nat))
  -- numerator identity: threeCasimir = threeF p + (threeF q + pq)
  have hnum : (SU3.threeCasimir p q : Int)
      = (SU3.threeF p : Int) + ((SU3.threeF q : Int) + (p * q : Nat)) := by
    have := threeCasimir_split_eq p q
    have hc : SU3.threeCasimir p q = SU3.threeF p + (SU3.threeF q + p * q) := by
      have := threeCasimir_split_eq p q; omega
    rw [hc]; push_cast; omega
  -- casimirQ p q = mkPos (threeCasimir) 3 = mkPos (split) 3 via hnum
  have h4 : casimirQ p q
      = Q'.mkPos ((SU3.threeF p : Int) + ((SU3.threeF q : Int) + (p * q : Nat))) 3 (by decide) := by
    show Q'.mkPos (SU3.threeCasimir p q : Int) 3 (by decide) = _
    rw [hnum]
  rw [h4]
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ h2 h3)

/-! ## The factorized exponent bound

`e^{−t·C₂(p,q)} ≤ bp·bq`, given per-axis bounds `bp ≥ e^{−t·f(p)}`,
`bq ≥ e^{−t·f(q)}`.  The proof: transport `e^{−t·C₂}` to `e^{−(a+(b+c))}`
(`a=t·f(p)`, `b=t·f(q)`, `c=t·pq/3`) across the `.eqv` exponent split via
`expNeg_eqv_congr`, split the product via the addition law
`expNeg_add_equiv`, and absorb the cross factor `e^{−c} ≤ 1`
(`expNeg_le_one`). -/

/-- `0 ≤ t·f(x)`. -/
theorem tfQ_nonneg (t : Q') (x : Nat) (ht : (0 : Q') ≤ t) : (0 : Q') ≤ t * fQ x :=
  Q'.mul_nonneg t (fQ x) ht (fQ_nonneg x)

/-- `0 ≤ t·(pq/3)`. -/
theorem tcrossQ_nonneg (t : Q') (p q : Nat) (ht : (0 : Q') ≤ t) :
    (0 : Q') ≤ t * crossQ p q :=
  Q'.mul_nonneg t (crossQ p q) ht (crossQ_nonneg p q)

/-- `0 ≤ t·C₂(p,q)`. -/
theorem tcasimirQ_nonneg (t : Q') (p q : Nat) (ht : (0 : Q') ≤ t) :
    (0 : Q') ≤ t * casimirQ p q :=
  Q'.mul_nonneg t (casimirQ p q) ht (casimirQ_nonneg p q)

/-- **Exponent half of the factorization.**  `e^{−t·C₂(p,q)} ≤ bp·bq`. -/
theorem expNeg_casimir_le (t : Q') (p q : Nat) (ht : (0 : Q') ≤ t)
    (bp bq : Q') (hbp0 : (0 : Q') ≤ bp) (hbq0 : (0 : Q') ≤ bq)
    (hbp : CReal.leRat (ExpNeg.expNeg (t * fQ p) (tfQ_nonneg t p ht)) bp)
    (hbq : CReal.leRat (ExpNeg.expNeg (t * fQ q) (tfQ_nonneg t q ht)) bq) :
    CReal.leRat (ExpNeg.expNeg (t * casimirQ p q) (tcasimirQ_nonneg t p q ht)) (bp * bq) := by
  -- exponent split: t·C₂ ≃ t·f(p) + (t·f(q) + t·pq/3)
  have hid : (t * casimirQ p q).eqv
      (t * fQ p + (t * fQ q + t * crossQ p q)) := by
    have e1 := Q'.mul_eqv_congr_left t (casimirQ p q) (fQ p + (fQ q + crossQ p q))
      (casimirQ_split_eqv p q)
    have e2 := Q'.mul_add_eqv t (fQ p) (fQ q + crossQ p q)
    have e3 := Q'.mul_add_eqv t (fQ q) (crossQ p q)
    have e4 := Q'.add_eqv_congr_left (t * fQ p) (t * (fQ q + crossQ p q))
      (t * fQ q + t * crossQ p q) e3
    exact Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 e4)
  have hbc_nn : (0 : Q') ≤ t * fQ q + t * crossQ p q :=
    Q'.zero_le_add _ _ (tfQ_nonneg t q ht) (tcrossQ_nonneg t p q ht)
  have hsum_nn : (0 : Q') ≤ t * fQ p + (t * fQ q + t * crossQ p q) :=
    Q'.zero_le_add _ _ (tfQ_nonneg t p ht) hbc_nn
  -- inner: e^{−(t·f(q)+t·pq/3)} ≤ bq·1
  have hbc : CReal.leRat (ExpNeg.expNeg (t * fQ q + t * crossQ p q) hbc_nn) (bq * 1) :=
    CReal.leRat_of_equiv
      (CReal.Equiv.symm (expNeg_add_equiv (t * fQ q) (t * crossQ p q)
        (tfQ_nonneg t q ht) (tcrossQ_nonneg t p q ht)))
      (CReal.leRat_mul hbq (expNeg_le_one (t * crossQ p q) (tcrossQ_nonneg t p q ht))
        (expNeg_geRat_zero _ _) (expNeg_geRat_zero _ _) hbq0 (by decide))
  -- outer: e^{−(a+(b+c))} ≤ bp·(bq·1)
  have hsum : CReal.leRat (ExpNeg.expNeg (t * fQ p + (t * fQ q + t * crossQ p q)) hsum_nn)
      (bp * (bq * 1)) :=
    CReal.leRat_of_equiv
      (CReal.Equiv.symm (expNeg_add_equiv (t * fQ p) (t * fQ q + t * crossQ p q)
        (tfQ_nonneg t p ht) hbc_nn))
      (CReal.leRat_mul hbp hbc (expNeg_geRat_zero _ _) (expNeg_geRat_zero _ _)
        hbp0 (Q'.mul_nonneg bq 1 hbq0 (by decide)))
  -- transport across the exponent split, then collapse bq·1 ≃ bq
  have hcasimir : CReal.leRat (ExpNeg.expNeg (t * casimirQ p q) (tcasimirQ_nonneg t p q ht))
      (bp * (bq * 1)) :=
    CReal.leRat_of_equiv
      (expNeg_eqv_congr (tcasimirQ_nonneg t p q ht) hsum_nn hid) hsum
  exact CReal.leRat_mono hcasimir
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left bp (bq * 1) bq (Q'.mul_one_eqv bq)))

/-! ## The per-term factorization capstone

`a(p,q) = dim(p,q)²·e^{−t·C₂(p,q)} ≤ (p+1)⁴(q+1)⁴·bp·bq` — the full
termwise majorant `a(p,q) ≤ g(p)·g(q)` with `g(x) = (x+1)⁴·bx`, combining
the prefactor half (`dimSqQ_le`) and the exponent half
(`expNeg_casimir_le`) through the product bound `leRat_mul`. -/

/-- `0 ≤ dim(p,q)²` over `Q'`. -/
theorem dimSqQ_nonneg (p q : Nat) : (0 : Q') ≤ dimSqQ p q := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg _

/-- `0 ≤ ofNat n`. -/
theorem ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg _

/-- **Per-term factorization.**  `dim(p,q)²·e^{−t·C₂(p,q)} ≤
(p+1)⁴(q+1)⁴·bp·bq`, given per-axis exp bounds `bp ≥ e^{−t·f(p)}`,
`bq ≥ e^{−t·f(q)}`.  This is the termwise majorant `a(p,q) ≤ g(p)·g(q)`
the U.6 box+tail 1-D sums consume. -/
theorem charTerm2D_le (t : Q') (p q : Nat) (ht : (0 : Q') ≤ t)
    (bp bq : Q') (hbp0 : (0 : Q') ≤ bp) (hbq0 : (0 : Q') ≤ bq)
    (hbp : CReal.leRat (ExpNeg.expNeg (t * fQ p) (tfQ_nonneg t p ht)) bp)
    (hbq : CReal.leRat (ExpNeg.expNeg (t * fQ q) (tfQ_nonneg t q ht)) bq) :
    CReal.leRat
      (CReal.mul (CReal.ofQ' (dimSqQ p q))
        (ExpNeg.expNeg (t * casimirQ p q) (tcasimirQ_nonneg t p q ht)))
      (Q'.ofNat (SU3.gPrefactor p * SU3.gPrefactor q) * (bp * bq)) :=
  CReal.leRat_mul
    (CReal.leRat_ofQ' (dimSqQ_le p q))
    (expNeg_casimir_le t p q ht bp bq hbp0 hbq0 hbp hbq)
    (ExpPos.geRat_of_eventually ⟨0, fun _ _ => dimSqQ_nonneg p q⟩)
    (expNeg_geRat_zero _ _)
    (ofNat_nonneg _)
    (Q'.mul_nonneg bp bq hbp0 hbq0)

end YMGap.Constructive.SU3CharFactor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.SU3CharFactor.charTerm2D_le
#print axioms YMGap.Constructive.SU3CharFactor.expNeg_casimir_le
#print axioms YMGap.Constructive.SU3CharFactor.mkPos3_add_eqv
#print axioms YMGap.Constructive.SU3CharFactor.casimirQ_split_eqv
#print axioms YMGap.Constructive.SU3CharFactor.fQ_nonneg
#print axioms YMGap.Constructive.SU3CharFactor.casimirQ_nonneg
#print axioms YMGap.Constructive.SU3CharFactor.threeCasimir_split_eq
#print axioms YMGap.Constructive.SU3CharFactor.dimSqQ_le
#print axioms YMGap.Constructive.SU3CharFactor.expNeg_le_one
