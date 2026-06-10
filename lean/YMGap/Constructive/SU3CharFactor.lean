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

end YMGap.Constructive.SU3CharFactor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.SU3CharFactor.fQ_nonneg
#print axioms YMGap.Constructive.SU3CharFactor.casimirQ_nonneg
#print axioms YMGap.Constructive.SU3CharFactor.threeCasimir_split_eq
#print axioms YMGap.Constructive.SU3CharFactor.dimSqQ_le
#print axioms YMGap.Constructive.SU3CharFactor.expNeg_le_one
