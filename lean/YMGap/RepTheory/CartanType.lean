/-
Cycle-free raw Cartan-family codes and validated nonredundant simple codes.

# Purpose and namespace compatibility

This Lean-core leaf owns the finite-type classification carrier that was
formerly declared in `RG/WeylDimGeneralData.lean`, together with the
historically named `IsSimpleRank` predicate formerly declared in
`MassGap/AllSimpleTypes.lean`.  The declarations deliberately retain their
original fully qualified names:

* `YMGap.RG.CartanType`, `YMGap.RG.CartanType.rank`, and
  `YMGap.RG.CartanType.numPosRoots`;
* `YMGap.MassGap.AllSimpleTypes.IsSimpleRank`.

Keeping those names makes the extraction behavior-preserving for existing
consumers while allowing representation-theoretic and future global-form
layers to import the classification without importing RG or mass-gap modules.

# Mathematical boundary

`CartanType` is a raw family/rank code.  Its classical constructors accept
every natural number, including values such as `A 0` and `D 0` that do not
denote a simple root system.  A nonredundant simple classification value is a
`CartanType` together with `IsCanonicalSimpleCode`; formulas such as `rank`
and `numPosRoots` are mechanically defined on all raw codes but receive their
intended classification meaning only on the validated domain.

Neither the raw code nor its validity proof is a compact gauge group or a
choice of global form.  In particular, this leaf carries no simply connected
group, finite central quotient, faithful action, topology, compactness, Haar
measure, or representation-descent data.  Distinct compact groups can have
the same validated Cartan code.

`IsSimpleRank` is retained only as a legacy compatibility alias for
`IsCanonicalSimpleCode`.  Its historical name must not be read as literal Lie
simplicity: for example, `C₂≅B₂` and `D₃≅A₃` are simple but are
excluded here to keep one canonical family code per isomorphism class.

# Constructivity

The file has no imports beyond Lean's implicit core prelude.  All data are
finite inductive/Natural-number computations; there is no Mathlib, classical
reasoning, choice, quotient, or noncomputable declaration.
-/

namespace YMGap.RG

/-! ## Raw Cartan-family/rank codes and root counts -/

/-- Raw family/rank codes for `A_n, B_n, C_n, D_n` and the five exceptionals
`G₂, F₄, E₆, E₇, E₈`.

The classical constructors admit every `Nat`; use
`IsCanonicalSimpleCode` before interpreting a value as a nonredundant simple
Lie/root-system classification.  This is never a choice of compact group or
global form. -/
inductive CartanType
  | A (n : Nat)
  | B (n : Nat)
  | C (n : Nat)
  | D (n : Nat)
  | G2
  | F4
  | E6
  | E7
  | E8
  deriving DecidableEq

/-- The Lie rank `r` (number of Cartan axes) of each type. -/
def CartanType.rank : CartanType → Nat
  | .A n => n
  | .B n => n
  | .C n => n
  | .D n => n
  | .G2 => 2
  | .F4 => 4
  | .E6 => 6
  | .E7 => 7
  | .E8 => 8

/-- The number of positive roots `#Δ⁺` of each type.

  * `A_n`: `n(n+1)/2` (`= N(N−1)/2` with `N = n+1`)
  * `B_n`, `C_n`: `n²`
  * `D_n`: `n(n−1)`
  * `G₂`: 6, `F₄`: 24, `E₆`: 36, `E₇`: 63, `E₈`: 120.

On a validated code this is the corresponding root-system count; on an
invalid raw code it is only the same arithmetic formula.  It contains no
information about the global form of a compact group. -/
def CartanType.numPosRoots : CartanType → Nat
  | .A n => n * (n + 1) / 2
  | .B n => n * n
  | .C n => n * n
  | .D n => n * (n - 1)
  | .G2 => 6
  | .F4 => 24
  | .E6 => 36
  | .E7 => 63
  | .E8 => 120

end YMGap.RG

namespace YMGap.MassGap.AllSimpleTypes

open YMGap.RG

/-! ## Canonical nonredundant simple codes

The four classical-family codes are canonical and nonredundant only above a
threshold (`B₁≅A₁`, `C₁≅A₁`, `C₂≅B₂`, `D₂≅A₁×A₁`, `D₃≅A₃`); we
retain `A_n : n≥1`, `B_n : n≥2`, `C_n : n≥3`, `D_n : n≥4`, and all five
exceptionals.  This is a canonical-code predicate, not a literal test of Lie
simplicity: the excluded aliases `C₂` and `D₃` still denote simple Lie
algebras under those noncanonical names.

This predicate concerns the Lie/root-system classification only.  It does not
select a simply connected group, adjoint group, or intermediate central
quotient. -/

/-- Validity of a raw Cartan code as the repository's canonical,
nonredundant representative of a simple Lie/root-system type. -/
def IsCanonicalSimpleCode : CartanType → Prop
  | .A n => 1 ≤ n
  | .B n => 2 ≤ n
  | .C n => 3 ≤ n
  | .D n => 4 ≤ n
  | .G2 => True
  | .F4 => True
  | .E6 => True
  | .E7 => True
  | .E8 => True

/-- Legacy compatibility alias for the historical public name.

New code should use `IsCanonicalSimpleCode`.  This alias expresses canonical
nonredundancy, not literal simplicity of every low-rank family alias. -/
abbrev IsSimpleRank : CartanType → Prop := IsCanonicalSimpleCode

end YMGap.MassGap.AllSimpleTypes
