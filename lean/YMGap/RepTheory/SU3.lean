/-
SU(3) irreducible-representation data (constructive Lean side), and the
two termwise inequalities behind the factorized character-tail majorant.

Mirrors `computations/su3_representations.py` and the rigorous bound of
`computations/su3_character_sum.py`:

  dim(p,q) = (p+1)(q+1)(p+q+2)/2
  C₂(p,q)  = (p² + q² + pq + 3p + 3q)/3
  f(x)     = (x² + 3x)/3

The character tail `Z_t = Σ_{(p,q)≠(0,0)} dim(p,q)²·e^{−t·C₂(p,q)}` is
bounded by the *factorized* majorant `a(p,q) ≤ g(p)·g(q)` with
`g(x) = (x+1)⁴·e^{−t·f(x)}`.  That factorization rests on exactly two
purely combinatorial facts, proved here axiom-empty in `Nat`:

  * `casimir_split_le` — `f(p)+f(q) ≤ C₂(p,q)`: drop the nonnegative cross
    term `pq/3`.  (Stated scaled by 3 to clear the denominator:
    `threeF p + threeF q ≤ threeCasimir p q`.)
  * `dimSq_le` — `dim(p,q)² ≤ (p+1)⁴(q+1)⁴`: from the core inequality
    `u+v ≤ 2uv` for `u = p+1, v = q+1` (`add_le_two_mul`).

The Casimirs are scaled to clear the `/3` and the dimension is handled
through its square (clearing the `/2`), so every load-bearing theorem
reports an empty axiom set, matching the `RepTheory/SU2.lean` encoding
discipline.  These are the `(p,q)`-polynomial inputs the U.6 character-tail
assembly consumes (the `dim`/`C₂`/`f` layer of `RepData`'s invariants,
specialized to the `A₂` weight lattice).

# Axiom-gate (AGENTS.md Rule 1)

Empty (`Nat` / `omega` / `decide`) throughout.  No `Classical.*`, no
`Quot.sound`, no `sorryAx`.
-/

namespace YMGap.RepTheory.SU3

/-! ## Irrep data as `(p,q)`-polynomials -/

/-- Dimension `dim(p,q) = (p+1)(q+1)(p+q+2)/2` (always an integer). -/
def dim (p q : Nat) : Nat := (p + 1) * (q + 1) * (p + q + 2) / 2

/-- `3·C₂(p,q) = p²+q²+pq+3p+3q` — the quadratic Casimir scaled to clear
the `/3`.  `C₂(p,q) = threeCasimir p q / 3`. -/
def threeCasimir (p q : Nat) : Nat := p * p + q * q + p * q + 3 * p + 3 * q

/-- `3·f(x) = x²+3x` — the per-index Casimir lower bound scaled to clear
the `/3`.  `f(x) = threeF x / 3`. -/
def threeF (x : Nat) : Nat := x * x + 3 * x

/-! ## Spec values (mirror `su3_representations.py`) -/

/-- Fundamental `(1,0)`: `dim = 3`. -/
theorem dim_fundamental : dim 1 0 = 3 := by decide
/-- Adjoint `(1,1)`: `dim = 8`. -/
theorem dim_adjoint : dim 1 1 = 8 := by decide
/-- Trivial `(0,0)`: `dim = 1`. -/
theorem dim_trivial : dim 0 0 = 1 := by decide
/-- Fundamental Casimir `C₂(1,0) = 4/3`, i.e. `threeCasimir = 4`. -/
theorem threeCasimir_fundamental : threeCasimir 1 0 = 4 := by decide
/-- Adjoint Casimir `C₂(1,1) = 3`, i.e. `threeCasimir = 9`. -/
theorem threeCasimir_adjoint : threeCasimir 1 1 = 9 := by decide

/-! ## Casimir split: `f(p)+f(q) ≤ C₂(p,q)` (drop `pq/3 ≥ 0`) -/

/-- The Casimir dominates the split per-index lower bound, the cross term
`pq` being nonnegative.  Scaled by 3 (clears the `/3` on both sides);
`omega` treats `p*p`, `q*q`, `p*q` as nonnegative atoms. -/
theorem casimir_split_le (p q : Nat) :
    threeF p + threeF q ≤ threeCasimir p q := by
  show (p * p + 3 * p) + (q * q + 3 * q) ≤ p * p + q * q + p * q + 3 * p + 3 * q
  omega

/-! ## Dimension bound: `dim(p,q)² ≤ (p+1)⁴(q+1)⁴` -/

/-- The core combinatorial fact `u+v ≤ 2uv` at `u = p+1, v = q+1`.
Since `v ≥ 1` gives `u ≤ uv` and `u ≥ 1` gives `v ≤ uv`, the sum is
`≤ uv + uv = 2uv`. -/
theorem add_le_two_mul (p q : Nat) :
    (p + 1) + (q + 1) ≤ 2 * (p + 1) * (q + 1) := by
  have hb : (p + 1) ≤ (p + 1) * (q + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos q)
  have ha : (q + 1) ≤ (p + 1) * (q + 1) :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos p)
  have hsum : (p + 1) + (q + 1) ≤ (p + 1) * (q + 1) + (p + 1) * (q + 1) :=
    Nat.add_le_add hb ha
  have hcollapse : (p + 1) * (q + 1) + (p + 1) * (q + 1) = 2 * (p + 1) * (q + 1) := by
    rw [Nat.mul_assoc]; omega
  omega

/-- The per-index majorant prefactor `gPrefactor x = (x+1)⁴` (written in
pure `*` form to keep the AC identities `ac_rfl`-closable, no Mathlib
`ring`).  This is the polynomial prefactor of `g(x) = (x+1)⁴·e^{−t·f(x)}`. -/
def gPrefactor (x : Nat) : Nat := (x + 1) * (x + 1) * (x + 1) * (x + 1)

/-- `dim(p,q) ≤ (p+1)²(q+1)²`.  From `p+q+2 = (p+1)+(q+1) ≤ 2(p+1)(q+1)`
(`add_le_two_mul`), multiply by `(p+1)(q+1)` and divide out the `/2`. -/
theorem dim_le (p q : Nat) :
    dim p q ≤ (p + 1) * (p + 1) * (q + 1) * (q + 1) := by
  have hpq : p + q + 2 ≤ 2 * (p + 1) * (q + 1) := by
    have := add_le_two_mul p q; omega
  -- (p+1)(q+1)(p+q+2) ≤ (p+1)(q+1) · 2(p+1)(q+1) = 2·((p+1)²(q+1)²)
  have hstep : (p + 1) * (q + 1) * (p + q + 2)
      ≤ (p + 1) * (q + 1) * (2 * (p + 1) * (q + 1)) :=
    Nat.mul_le_mul_left ((p + 1) * (q + 1)) hpq
  have hrw : (p + 1) * (q + 1) * (2 * (p + 1) * (q + 1))
      = 2 * ((p + 1) * (p + 1) * (q + 1) * (q + 1)) := by ac_rfl
  have hmul : (p + 1) * (q + 1) * (p + q + 2)
      ≤ 2 * ((p + 1) * (p + 1) * (q + 1) * (q + 1)) := by rw [hrw] at hstep; exact hstep
  show (p + 1) * (q + 1) * (p + q + 2) / 2 ≤ (p + 1) * (p + 1) * (q + 1) * (q + 1)
  exact Nat.div_le_of_le_mul hmul

/-- `dim(p,q)² ≤ (p+1)⁴(q+1)⁴ = gPrefactor p · gPrefactor q` — the
dimension half of the factorized character-tail majorant (`dim²` is the
per-irrep prefactor of `Z_t`, and it factorizes across `p` and `q`). -/
theorem dimSq_le (p q : Nat) :
    dim p q * dim p q ≤ gPrefactor p * gPrefactor q := by
  have h := dim_le p q
  have hsq : dim p q * dim p q
      ≤ ((p + 1) * (p + 1) * (q + 1) * (q + 1))
        * ((p + 1) * (p + 1) * (q + 1) * (q + 1)) :=
    Nat.mul_le_mul h h
  have hrw : ((p + 1) * (p + 1) * (q + 1) * (q + 1))
        * ((p + 1) * (p + 1) * (q + 1) * (q + 1))
      = gPrefactor p * gPrefactor q := by
    show _ = ((p + 1) * (p + 1) * (p + 1) * (p + 1))
            * ((q + 1) * (q + 1) * (q + 1) * (q + 1))
    ac_rfl
  rw [hrw] at hsq; exact hsq

end YMGap.RepTheory.SU3

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RepTheory.SU3.casimir_split_le
#print axioms YMGap.RepTheory.SU3.add_le_two_mul
#print axioms YMGap.RepTheory.SU3.dim_le
#print axioms YMGap.RepTheory.SU3.dimSq_le
#print axioms YMGap.RepTheory.SU3.dim_fundamental
#print axioms YMGap.RepTheory.SU3.threeCasimir_fundamental
