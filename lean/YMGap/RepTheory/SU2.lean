/-
SU(2) irreducible representations (constructive Lean side).

Mirrors `computations/su2_representations.py` for Milestone 1.1.

Constructive contract (from `lean/AGENTS.md`):

  - All existence claims return witnesses (`Σ` / structures), never
    propositional `∃`.
  - All quantities are exact `Nat`.
  - Load-bearing theorems are followed by `#print axioms` gates;
    every gate must report "depends on axioms: []" (or, equivalently,
    "does not depend on any axioms").

Killing-form normalization: physics-spin convention (`T_a = σ_a/2`),
`C_2(j) = j(j+1)` on the spin-j irrep.  See the Python module
docstring and `notes/su2-representations.md` §1 for the conventions
table.

## Why a Nat-only encoding of the Casimir

`C_2(j) = j(j+1)` is always a nonnegative rational whose denominator
divides 4 (since `j` is a half-integer).  With `s = 2j ∈ ℕ`:

```
  C_2(j)  =  s · (s + 2) / 4.
```

This file exposes `fourTimesCasimir s := s · (s + 2)`, a `Nat`, so
that every spec value is provable by `rfl` inside Nat-arithmetic.

Lean 4 core's `Rat` was tried first; even the *reflexive* equality
`(3 : Rat) / 4 = (3 : Rat) / 4` proved by `rfl` reports

```
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

which AGENTS.md Rule 1 forbids in load-bearing theorems.  The
Nat-only spec carries the same information (`C_2(j) = fourTimesCasimir
s / 4` as documentation) and reduces to an empty axiom set.  If a
later milestone genuinely needs a `Rat`-valued surface, it will live
under `YMGap/Classical/` per AGENTS.md Rule 4, re-exported through a
constructive interface.
-/

namespace YMGap.RepTheory.SU2

/-! ## Spin index -/

/-- The spin index of an SU(2) irrep, encoded as `2j ∈ ℕ`.

  * `Spin 0` — trivial irrep (`j = 0`)
  * `Spin 1` — fundamental (`j = 1/2`)
  * `Spin 2` — adjoint (`j = 1`)
  * `Spin 3` — `j = 3/2`
  * ...
-/
abbrev Spin : Type := Nat

/-! ## Dimension and Casimir as computable Nat data -/

/-- The dimension `d_j = 2j + 1` of the spin-`j` irrep. -/
def dimension (s : Spin) : Nat := s + 1

/-- `4 · C_2(j)` for spin `j = s/2`, as a `Nat`.

The Rat-valued Casimir is `C_2(j) = fourTimesCasimir s / 4`; the
integer-numerator form keeps the spec inside pure Nat-arithmetic
(see the file docstring for the axiom-cleanliness rationale). -/
def fourTimesCasimir (s : Spin) : Nat := s * (s + 2)

/-! ## Spec-quoted values

Each of these mirrors a value quoted in `docs/outline.md` §18.1.
All are closed by reflection: they hold because the function
*computes* to the stated value. -/

/-- `d_0 = 1`: the trivial irrep is one-dimensional. -/
theorem dimension_zero : dimension 0 = 1 := rfl

/-- `d_{1/2} = 2`: the fundamental is two-dimensional. -/
theorem dimension_one_half : dimension 1 = 2 := rfl

/-- `d_1 = 3`: the adjoint is three-dimensional. -/
theorem dimension_one : dimension 2 = 3 := rfl

/-- `d_{3/2} = 4`. -/
theorem dimension_three_halves : dimension 3 = 4 := rfl

/-- `d_2 = 5`. -/
theorem dimension_two : dimension 4 = 5 := rfl

/-- `4 · C_2(0) = 0`. -/
theorem fourTimesCasimir_zero : fourTimesCasimir 0 = 0 := rfl

/-- `4 · C_2(1/2) = 3`, i.e. `C_2(1/2) = 3/4`.

This is the smallest *nonzero* Casimir, the quantity quoted as
`κ_{SU(2)} ~ 3/4` in `docs/outline.md` §18.1 and verified
symbolically by `verify_casimir_one_half()` in the Python companion
module. -/
theorem fourTimesCasimir_one_half : fourTimesCasimir 1 = 3 := rfl

/-- `4 · C_2(1) = 8`, i.e. `C_2(1) = 2`. -/
theorem fourTimesCasimir_one : fourTimesCasimir 2 = 8 := rfl

/-- `4 · C_2(3/2) = 15`, i.e. `C_2(3/2) = 15/4`. -/
theorem fourTimesCasimir_three_halves : fourTimesCasimir 3 = 15 := rfl

/-- `4 · C_2(2) = 24`, i.e. `C_2(2) = 6`. -/
theorem fourTimesCasimir_two : fourTimesCasimir 4 = 24 := rfl

/-! ## Witness-bearing structures (constructive existence)

The data fields are the witnesses; the `*_spec` fields are
propositional certificates that the witnesses obey the spec
formulas. -/

/-- A complete witness for the spin-`j` irrep.  Constructive
analogue of the Python `Irrep` dataclass. -/
structure Irrep where
  /-- Spin index, encoded as `2j`. -/
  spin : Spin
  /-- Dimension witness `d_j`. -/
  dim : Nat
  /-- `4 · C_2(j)` witness. -/
  fourCas : Nat
  /-- Certificate that `dim` is `dimension spin`. -/
  dim_spec : dim = dimension spin
  /-- Certificate that `fourCas` is `fourTimesCasimir spin`. -/
  cas_spec : fourCas = fourTimesCasimir spin

/-- Construct an `Irrep` from a spin index by computing both
witnesses on the spot.  The `*_spec` fields are `rfl`, so the
structure is honest data, not an opaque promise. -/
def Irrep.ofSpin (s : Spin) : Irrep where
  spin := s
  dim := dimension s
  fourCas := fourTimesCasimir s
  dim_spec := rfl
  cas_spec := rfl

/-- The Subtype witness for the smallest nonzero Casimir.

The element carries (a) the natural number `3` and (b) the proof
that `3 = fourTimesCasimir 1`, i.e. `3 = 4 · C_2(1/2)`, i.e.
`C_2(1/2) = 3/4`.  No `Exists` is used; the witness is data. -/
def smallestNonzeroFourCasimir : { n : Nat // n = fourTimesCasimir 1 } :=
  ⟨3, fourTimesCasimir_one_half.symm⟩

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Each load-bearing claim below is followed by `#print axioms`.
Expected output for every line: "does not depend on any axioms".

If a future edit causes any of these to start depending on
`Classical.choice`, `Classical.em`, `propext`, `Quot.sound`, or
`sorryAx`, that is a build-log signal to either remove the
dependency or quarantine it under `YMGap/Classical/` (Rule 4). -/

#print axioms dimension_zero
#print axioms dimension_one_half
#print axioms dimension_one
#print axioms dimension_three_halves
#print axioms dimension_two
#print axioms fourTimesCasimir_zero
#print axioms fourTimesCasimir_one_half
#print axioms fourTimesCasimir_one
#print axioms fourTimesCasimir_three_halves
#print axioms fourTimesCasimir_two
#print axioms Irrep.ofSpin
#print axioms smallestNonzeroFourCasimir

end YMGap.RepTheory.SU2
