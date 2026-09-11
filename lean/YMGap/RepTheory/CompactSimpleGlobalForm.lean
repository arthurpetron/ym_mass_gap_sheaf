/-
Finite codes for global forms of compact simple Lie type.

# Scope

This module records a finite **marked** datum needed to distinguish global
forms with the same validated Cartan code.  For a simply connected compact
simple group with center `Z`, a marked global form is coded by a subgroup
`Gamma ≤ Z` intended to be divided out.  Cyclic subgroup codes carry an
explicit positive order, positive index, and multiplication certificate,
rather than a free tag claiming divisibility.

The exact simply connected center shapes used here are:

* `A_n`: cyclic of order `n+1`;
* `B_n`, `C_n`: cyclic of order `2`;
* `D_n`: Klein four for even `n`, cyclic of order `4` for odd `n`;
* `E₆`: cyclic of order `3`; `E₇`: cyclic of order `2`;
* `E₈`, `F₄`, `G₂`: trivial.

For even `D_n`, the Klein-four center has three marked order-two subgroups.
They are kept as three codes here.  Diagram automorphisms exchange the two
spinorial axes for higher even `D_n`, and `D₄` triality permutes all three.
Consequently this file classifies marked subgroup data; it does not claim that
its codes are unique representatives of compact groups up to unmarked group
isomorphism.  A later completeness/nonduplication theorem must either retain
the marking or quotient these codes by the relevant root-datum automorphisms.

# Boundary

`CompactSimpleGlobalFormCode` is a **finite global-form code**, not a
realization of a compact group.  In particular, this module constructs no
actual `SU(2)` or `SO(3)` carrier, no group law or quotient map, no quotient
topology or compactness proof, no faithful matrix action, no Haar functional,
and no representation objects.  The A₁ descent test below is only the exact
central-character parity rule at the label/code level.  Realizing these codes
belongs to later constructive-group, topology, action, and Peter--Weyl layers.

# Constructivity

The only project import is the cycle-free Cartan leaf.  There is no Mathlib,
classical reasoning, choice, `native_decide`, quotient, `noncomputable`, or
`sorry`.  Closed natural-number checks use kernel `decide`.
-/

import YMGap.RepTheory.CartanType

namespace YMGap.RepTheory

open YMGap.RG
open YMGap.MassGap.AllSimpleTypes

/-! ## Simply connected center shapes -/

/-- The three possible abstract center shapes needed for simply connected
compact simple groups.

The constructor is proof-free so dependent subgroup codes reduce by structural
pattern matching.  Positivity of a cyclic order is the separate predicate
`CenterShape.Valid` below. -/
inductive CenterShape
  | trivial
  | cyclic (order : Nat)
  | kleinFour

/-- Validity of a center-shape code.  Only a cyclic shape has a nontrivial
side condition: its recorded finite order must be positive. -/
def CenterShape.Valid : CenterShape → Prop
  | .trivial => True
  | .cyclic n => 0 < n
  | .kleinFour => True

/-- Cardinality of a center shape. -/
def CenterShape.order : CenterShape → Nat
  | .trivial => 1
  | .cyclic n => n
  | .kleinFour => 4

/-- Every admitted center shape has positive cardinality. -/
theorem CenterShape.order_pos (shape : CenterShape) (hvalid : shape.Valid) :
    0 < shape.order := by
  cases shape with
  | trivial => exact Nat.zero_lt_one
  | cyclic n => exact hvalid
  | kleinFour => exact Nat.succ_pos 3

/-- The center shape of the simply connected compact group with Cartan type
`T`.

This is classification data only.  For `D_n`, parity distinguishes
`Spin(4k)` with Klein-four center from `Spin(4k+2)` with cyclic order-four
center. -/
def simplyConnectedCenter : CartanType → CenterShape
  | .A n => .cyclic (n + 1)
  | .B _ => .cyclic 2
  | .C _ => .cyclic 2
  | .D n =>
      if n % 2 = 0 then .kleinFour else .cyclic 4
  | .G2 => .trivial
  | .F4 => .trivial
  | .E6 => .cyclic 3
  | .E7 => .cyclic 2
  | .E8 => .trivial

/-- Every Cartan-classified simply connected center has a valid finite shape. -/
theorem simplyConnectedCenter_valid (T : CartanType) :
    (simplyConnectedCenter T).Valid := by
  cases T with
  | A n => exact Nat.succ_pos n
  | B n => exact Nat.zero_lt_two
  | C n => exact Nat.zero_lt_two
  | D n =>
      change CenterShape.Valid
        (if n % 2 = 0 then .kleinFour else .cyclic 4)
      by_cases h : n % 2 = 0
      · rw [if_pos h]
        exact True.intro
      · rw [if_neg h]
        exact Nat.succ_pos 3
  | G2 => exact True.intro
  | F4 => exact True.intro
  | E6 => exact Nat.succ_pos 2
  | E7 => exact Nat.zero_lt_two
  | E8 => exact True.intro

/-! ## Honest subgroup codes for each center shape -/

/-- A subgroup code for a cyclic group of order `ambientOrder`.

The subgroup is the unique cyclic subgroup of the recorded positive `order`.
The positive `index` and equation `order * index = ambientOrder` are explicit
computational evidence that the order divides the ambient order.  Thus this
is not a free subgroup tag. -/
structure CyclicSubgroupCode (ambientOrder : Nat) where
  /-- Order of the cyclic subgroup. -/
  order : Nat
  /-- Index of the subgroup in the ambient cyclic group. -/
  index : Nat
  /-- The subgroup order is positive. -/
  order_pos : 0 < order
  /-- The subgroup index is positive. -/
  index_pos : 0 < index
  /-- Explicit divisor certificate. -/
  factorization : order * index = ambientOrder
  /-- Basic order bound, retained as directly consumable data. -/
  order_le_ambient : order ≤ ambientOrder

/-- The five and only five subgroups of the Klein four group.

The three order-two cases are the spans of the three nonzero elements
`e₁`, `e₂`, and `e₁+e₂` in a chosen marking of the center.  Diagram
automorphisms can identify different marked cases as explained in the module
scope; no unmarked-isomorphism quotient is asserted here. -/
inductive KleinSubgroupCode
  | trivial
  | firstAxis
  | secondAxis
  | diagonalAxis
  | full

/-- Subgroup codes indexed by their ambient center shape.

Making this a genuine indexed inductive, rather than a reducible dependent
type family, lets every eliminator match structurally on the subgroup code
itself.  The trivial-center fiber has exactly the single constructor `unique`;
the cyclic fiber contains an honest divisor certificate; and the Klein fiber
contains exactly one of the five codes above. -/
inductive CenterSubgroupCode : CenterShape → Type
  | unique : CenterSubgroupCode .trivial
  | cyclicCode {n : Nat} (code : CyclicSubgroupCode n) :
      CenterSubgroupCode (.cyclic n)
  | kleinCode (code : KleinSubgroupCode) :
      CenterSubgroupCode .kleinFour

namespace KleinSubgroupCode

/-- Order of a Klein-four subgroup code. -/
def order : KleinSubgroupCode → Nat
  | .trivial => 1
  | .firstAxis => 2
  | .secondAxis => 2
  | .diagonalAxis => 2
  | .full => 4

/-- Index of a Klein-four subgroup code. -/
def index : KleinSubgroupCode → Nat
  | .trivial => 4
  | .firstAxis => 2
  | .secondAxis => 2
  | .diagonalAxis => 2
  | .full => 1

end KleinSubgroupCode

namespace CenterSubgroupCode

/-- The trivial subgroup, constructively for every valid center shape. -/
def trivial : (shape : CenterShape) → shape.Valid → CenterSubgroupCode shape
  | .trivial, _ => .unique
  | .cyclic n, hn =>
      .cyclicCode
        { order := 1
          index := n
          order_pos := Nat.zero_lt_one
          index_pos := hn
          factorization := Nat.one_mul n
          order_le_ambient := Nat.succ_le_of_lt hn }
  | .kleinFour, _ => .kleinCode .trivial

/-- The full subgroup, constructively for every valid center shape. -/
def full : (shape : CenterShape) → shape.Valid → CenterSubgroupCode shape
  | .trivial, _ => .unique
  | .cyclic n, hn =>
      .cyclicCode
        { order := n
          index := 1
          order_pos := hn
          index_pos := Nat.zero_lt_one
          factorization := Nat.mul_one n
          order_le_ambient := Nat.le_refl n }
  | .kleinFour, _ => .kleinCode .full

/-- Order of a subgroup code, by nonrecursive structural elimination on the
indexed code. -/
def order {shape : CenterShape} (Gamma : CenterSubgroupCode shape) : Nat :=
  match Gamma with
  | .unique => 1
  | .cyclicCode code => code.order
  | .kleinCode code => KleinSubgroupCode.order code

/-- Index of a subgroup code in its ambient center, again eliminating only on
the indexed code. -/
def index {shape : CenterShape} (Gamma : CenterSubgroupCode shape) : Nat :=
  match Gamma with
  | .unique => 1
  | .cyclicCode code => code.index
  | .kleinCode code => KleinSubgroupCode.index code

/-- The recorded subgroup order and index multiply to the center order. -/
theorem order_mul_index {shape : CenterShape}
    (Gamma : CenterSubgroupCode shape) :
    order Gamma * index Gamma = shape.order := by
  cases Gamma with
  | unique => rfl
  | cyclicCode code => exact code.factorization
  | kleinCode code => cases code <;> rfl

/-- Every subgroup code has positive order. -/
theorem order_pos {shape : CenterShape}
    (Gamma : CenterSubgroupCode shape) :
    0 < order Gamma := by
  cases Gamma with
  | unique => exact Nat.zero_lt_one
  | cyclicCode code => exact code.order_pos
  | kleinCode code =>
      cases code with
      | trivial => exact Nat.zero_lt_one
      | firstAxis => exact Nat.zero_lt_two
      | secondAxis => exact Nat.zero_lt_two
      | diagonalAxis => exact Nat.zero_lt_two
      | full => exact Nat.succ_pos 3

/-- Every subgroup code has positive index. -/
theorem index_pos {shape : CenterShape}
    (Gamma : CenterSubgroupCode shape) :
    0 < index Gamma := by
  cases Gamma with
  | unique => exact Nat.zero_lt_one
  | cyclicCode code => exact code.index_pos
  | kleinCode code =>
      cases code with
      | trivial => exact Nat.succ_pos 3
      | firstAxis => exact Nat.zero_lt_two
      | secondAxis => exact Nat.zero_lt_two
      | diagonalAxis => exact Nat.zero_lt_two
      | full => exact Nat.zero_lt_one

/-- A subgroup's order is bounded by the order of its ambient center. -/
theorem order_le_center {shape : CenterShape}
    (Gamma : CenterSubgroupCode shape) :
    order Gamma ≤ shape.order := by
  cases Gamma with
  | unique => exact Nat.le_refl 1
  | cyclicCode code => exact code.order_le_ambient
  | kleinCode code =>
      cases code with
      | trivial =>
          exact Nat.le_trans (Nat.le_succ 1)
            (Nat.le_trans (Nat.le_succ 2) (Nat.le_succ 3))
      | firstAxis =>
          exact Nat.le_trans (Nat.le_succ 2) (Nat.le_succ 3)
      | secondAxis =>
          exact Nat.le_trans (Nat.le_succ 2) (Nat.le_succ 3)
      | diagonalAxis =>
          exact Nat.le_trans (Nat.le_succ 2) (Nat.le_succ 3)
      | full => exact Nat.le_refl 4

/-- The trivial subgroup has order one for every center shape. -/
theorem trivial_order (shape : CenterShape) (hvalid : shape.Valid) :
    order (trivial shape hvalid) = 1 := by
  cases shape <;> rfl

/-- The full subgroup has the same order as its ambient center. -/
theorem full_order (shape : CenterShape) (hvalid : shape.Valid) :
    order (full shape hvalid) = shape.order := by
  cases shape <;> rfl

end CenterSubgroupCode

/-! ## Global-form codes -/

/-- Finite marked global-form code for a canonical simple Cartan code.

`Gamma` is the coded finite central subgroup intended as the kernel of the
simply connected cover.  This structure preserves canonical-code validity but
contains no group realization, root-datum automorphism quotient, or analytic
data. -/
structure CompactSimpleGlobalFormCode where
  /-- Raw Lie/root-system family/rank code. -/
  cartan : CartanType
  /-- Proof that the code is the chosen nonredundant simple representative. -/
  canonicalCode : IsCanonicalSimpleCode cartan
  /-- Central subgroup intended to be divided out. -/
  Gamma : CenterSubgroupCode (simplyConnectedCenter cartan)

namespace CompactSimpleGlobalFormCode

/-- The simply connected center attached to any global-form code is valid,
derived from its Cartan type rather than stored as duplicate proof data. -/
theorem center_valid (code : CompactSimpleGlobalFormCode) :
    (simplyConnectedCenter code.cartan).Valid :=
  simplyConnectedCenter_valid code.cartan

/-- Code for the simply connected global form: divide by the trivial center
subgroup. -/
def simplyConnected (T : CartanType) (hT : IsCanonicalSimpleCode T) :
    CompactSimpleGlobalFormCode where
  cartan := T
  canonicalCode := hT
  Gamma := CenterSubgroupCode.trivial (simplyConnectedCenter T)
    (simplyConnectedCenter_valid T)

/-- Code for the adjoint global form: divide by the full center. -/
def adjoint (T : CartanType) (hT : IsCanonicalSimpleCode T) :
    CompactSimpleGlobalFormCode where
  cartan := T
  canonicalCode := hT
  Gamma := CenterSubgroupCode.full (simplyConnectedCenter T)
    (simplyConnectedCenter_valid T)

/-- The simply connected constructor records a trivial kernel of order one. -/
theorem simplyConnected_Gamma_order (T : CartanType)
    (hT : IsCanonicalSimpleCode T) :
    CenterSubgroupCode.order (simplyConnected T hT).Gamma = 1 :=
  CenterSubgroupCode.trivial_order (simplyConnectedCenter T)
    (simplyConnectedCenter_valid T)

/-- The adjoint constructor records the full simply connected center. -/
theorem adjoint_Gamma_order (T : CartanType)
    (hT : IsCanonicalSimpleCode T) :
    CenterSubgroupCode.order (adjoint T hT).Gamma =
      (simplyConnectedCenter T).order :=
  CenterSubgroupCode.full_order (simplyConnectedCenter T)
    (simplyConnectedCenter_valid T)

end CompactSimpleGlobalFormCode

/-! ## A₁ code-level validation: `SU(2)` versus `SO(3)` -/

/-- `A₁` is the canonical code for its simple Lie/root-system type. -/
theorem a1_isCanonicalSimpleCode : IsCanonicalSimpleCode (.A 1) := by
  show 1 ≤ 1
  exact Nat.le_refl 1

/-- Legacy compatibility theorem using the historical predicate name. -/
theorem a1_isSimpleRank : IsSimpleRank (.A 1) :=
  a1_isCanonicalSimpleCode

/-- The simply connected A₁ global-form code, conventionally called the
`SU(2)` code.  No actual `SU(2)` carrier is constructed here. -/
def su2GlobalFormCode : CompactSimpleGlobalFormCode :=
  CompactSimpleGlobalFormCode.simplyConnected (.A 1)
    a1_isCanonicalSimpleCode

/-- The adjoint A₁ global-form code, conventionally called the `SO(3)`
code.  No actual `SO(3)` quotient or topology is constructed here. -/
def so3GlobalFormCode : CompactSimpleGlobalFormCode :=
  CompactSimpleGlobalFormCode.adjoint (.A 1) a1_isCanonicalSimpleCode

/-- The `SU(2)` code's `Gamma` is definitionally the trivial subgroup code. -/
theorem su2GlobalFormCode_Gamma_is_trivial :
    su2GlobalFormCode.Gamma =
      CenterSubgroupCode.trivial (simplyConnectedCenter (.A 1))
        (simplyConnectedCenter_valid (.A 1)) := rfl

/-- The `SO(3)` code's `Gamma` is definitionally the full-center code. -/
theorem so3GlobalFormCode_Gamma_is_full :
    so3GlobalFormCode.Gamma =
      CenterSubgroupCode.full (simplyConnectedCenter (.A 1))
        (simplyConnectedCenter_valid (.A 1)) := rfl

/-- The `SU(2)` code divides by the trivial subgroup of its order-two center. -/
theorem su2GlobalFormCode_Gamma_order :
    CenterSubgroupCode.order su2GlobalFormCode.Gamma = 1 :=
  CompactSimpleGlobalFormCode.simplyConnected_Gamma_order (.A 1)
    a1_isCanonicalSimpleCode

/-- The `SO(3)` code divides by the full order-two center. -/
theorem so3GlobalFormCode_Gamma_order :
    CenterSubgroupCode.order so3GlobalFormCode.Gamma = 2 :=
  CompactSimpleGlobalFormCode.adjoint_Gamma_order (.A 1)
    a1_isCanonicalSimpleCode

/-- The two A₁ global forms are distinguished by their coded kernel orders. -/
theorem su2_so3_Gamma_orders_ne :
    CenterSubgroupCode.order su2GlobalFormCode.Gamma ≠
      CenterSubgroupCode.order so3GlobalFormCode.Gamma := by
  intro h
  have hOneTwo : (1 : Nat) = 2 :=
    su2GlobalFormCode_Gamma_order.symm.trans
      (h.trans so3GlobalFormCode_Gamma_order)
  exact (by decide : (1 : Nat) ≠ 2) hOneTwo

/-- Code-level evenness of the doubled-spin label `s = 2j`. -/
def DoubledSpinIsEven (s : Nat) : Prop := s % 2 = 0

/-- Code-level SO(3) descent rule for an SU(2) doubled-spin label.

The modulus is the order of the coded quotient kernel, tying the parity rule
directly to `so3GlobalFormCode.Gamma`.  This is not yet a descended
representation object. -/
def SO3DoubledSpinDescends (s : Nat) : Prop :=
  s % (CenterSubgroupCode.order so3GlobalFormCode.Gamma) = 0

/-- An SU(2) doubled-spin label descends through the SO(3) code exactly when
it is even. -/
theorem so3DoubledSpin_descends_iff_even (s : Nat) :
    SO3DoubledSpinDescends s ↔ DoubledSpinIsEven s := by
  unfold SO3DoubledSpinDescends DoubledSpinIsEven
  rw [so3GlobalFormCode_Gamma_order]

/-- Spin one-half (`s = 1`) is rejected by the SO(3) descent code. -/
theorem so3_spinHalf_rejected : ¬ SO3DoubledSpinDescends 1 := by
  intro h
  have heven : DoubledSpinIsEven 1 :=
    (so3DoubledSpin_descends_iff_even 1).mp h
  unfold DoubledSpinIsEven at heven
  exact (by decide : (1 % 2 : Nat) ≠ 0) heven

/-- Spin one (`s = 2`) is accepted by the SO(3) descent code. -/
theorem so3_spinOne_accepted : SO3DoubledSpinDescends 2 := by
  apply (so3DoubledSpin_descends_iff_even 2).mpr
  unfold DoubledSpinIsEven
  decide

end YMGap.RepTheory

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RepTheory.CenterShape.order_pos
#print axioms YMGap.RepTheory.simplyConnectedCenter_valid
#print axioms YMGap.RepTheory.CenterSubgroupCode.order_mul_index
#print axioms YMGap.RepTheory.CenterSubgroupCode.order_pos
#print axioms YMGap.RepTheory.CenterSubgroupCode.index_pos
#print axioms YMGap.RepTheory.CenterSubgroupCode.order_le_center
#print axioms YMGap.RepTheory.CenterSubgroupCode.trivial_order
#print axioms YMGap.RepTheory.CenterSubgroupCode.full_order
#print axioms YMGap.RepTheory.CompactSimpleGlobalFormCode.center_valid
#print axioms YMGap.RepTheory.CompactSimpleGlobalFormCode.simplyConnected_Gamma_order
#print axioms YMGap.RepTheory.CompactSimpleGlobalFormCode.adjoint_Gamma_order
#print axioms YMGap.RepTheory.a1_isCanonicalSimpleCode
#print axioms YMGap.RepTheory.a1_isSimpleRank
#print axioms YMGap.RepTheory.su2GlobalFormCode_Gamma_is_trivial
#print axioms YMGap.RepTheory.so3GlobalFormCode_Gamma_is_full
#print axioms YMGap.RepTheory.su2GlobalFormCode_Gamma_order
#print axioms YMGap.RepTheory.so3GlobalFormCode_Gamma_order
#print axioms YMGap.RepTheory.su2_so3_Gamma_orders_ne
#print axioms YMGap.RepTheory.so3DoubledSpin_descends_iff_even
#print axioms YMGap.RepTheory.so3_spinHalf_rejected
#print axioms YMGap.RepTheory.so3_spinOne_accepted
