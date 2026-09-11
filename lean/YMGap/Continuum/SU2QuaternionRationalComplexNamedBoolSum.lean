/-
# Named Boolean sums of rational-complex values

A nested Boolean sum normally records only binder position.  The elementary
cube instead needs to compare two orders of the same twenty-four matrix-index
names.  This leaf gives each binder a natural-number tag and proves that the
resulting rational-complex sum is invariant under a constructive permutation
of those tags.

The construction is purely post-Haar and additive.  It never constructs a
Boolean assignment carrier, never enumerates a concrete binder tree, and
asserts no polynomial identity.  Repeated tags are allowed: the adjacent-swap
proof handles equality separately, while distinct tags commute as ordinary
finite updates of an environment.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra

namespace YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolSum

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra

/-! ## 1. Tagged finite updates -/

/-- Replace one named Boolean coordinate in a total environment. -/
def boolTagUpdate
    (environment : Nat → Bool) (tag : Nat) (value : Bool) : Nat → Bool :=
  fun query => if query = tag then value else environment query

theorem boolTagUpdate_self
    (environment : Nat → Bool) (tag : Nat) (value : Bool) :
    boolTagUpdate environment tag value tag = value := by
  simp only [boolTagUpdate, ↓reduceIte]

theorem boolTagUpdate_of_ne
    (environment : Nat → Bool) (tag query : Nat) (value : Bool)
    (hne : query ≠ tag) :
    boolTagUpdate environment tag value query = environment query := by
  simp only [boolTagUpdate, hne, ↓reduceIte]

/-- Updates at distinct names commute extensionally. -/
theorem boolTagUpdate_comm
    (environment : Nat → Bool)
    (first second : Nat) (firstValue secondValue : Bool)
    (hne : first ≠ second) :
    boolTagUpdate
        (boolTagUpdate environment first firstValue)
        second secondValue =
      boolTagUpdate
        (boolTagUpdate environment second secondValue)
        first firstValue := by
  funext query
  by_cases hfirst : query = first
  · subst query
    simp only [boolTagUpdate, hne, ↓reduceIte]
  · by_cases hsecond : query = second
    · subst query
      simp only [boolTagUpdate, Ne.symm hne, ↓reduceIte]
    · simp only [boolTagUpdate, hfirst, hsecond, ↓reduceIte]

/-! ## 2. Structural named sums -/

/-- Sum a rational-complex family over Boolean values assigned to the given
tag list, in list order.  The empty environment is constantly false; every
encountered binder updates its named coordinate before the family is read. -/
def rationalComplexNamedBoolSum :
    List Nat → ((Nat → Bool) → RationalComplex) → RationalComplex
  | [], family => family (fun _ => false)
  | tag :: tags, family =>
      rationalComplexBoolBind (fun value =>
        rationalComplexNamedBoolSum tags (fun environment =>
          family (boolTagUpdate environment tag value)))

/-- Pointwise rational-complex equivalence passes through every named binder. -/
theorem rationalComplexNamedBoolSum_congr :
    ∀ (tags : List Nat)
      {left right : (Nat → Bool) → RationalComplex},
      (∀ environment, RationalComplexEqv
        (left environment) (right environment)) →
      RationalComplexEqv
        (rationalComplexNamedBoolSum tags left)
        (rationalComplexNamedBoolSum tags right)
  | [], left, right, hpointwise =>
      hpointwise (fun _ => false)
  | tag :: tags, left, right, hpointwise => by
      simp only [rationalComplexNamedBoolSum]
      exact rationalComplexBoolBind_congr (fun value =>
        rationalComplexNamedBoolSum_congr tags (fun environment =>
          hpointwise (boolTagUpdate environment tag value)))

/-! ## 3. Adjacent exchange and arbitrary permutations -/

/-- Adjacent named binders may be exchanged.  Equal tags give the same list;
distinct tags use two-binder additivity together with commutation of their
environment updates. -/
theorem rationalComplexNamedBoolSum_swap
    (first second : Nat) (rest : List Nat)
    (family : (Nat → Bool) → RationalComplex) :
    RationalComplexEqv
      (rationalComplexNamedBoolSum (first :: second :: rest) family)
      (rationalComplexNamedBoolSum (second :: first :: rest) family) := by
  by_cases hne : first = second
  · subst second
    exact rationalComplexEqv_refl _
  · simp only [rationalComplexNamedBoolSum]
    refine rationalComplexEqv_trans
      (rationalComplexBoolBind_swap (fun firstValue secondValue =>
        rationalComplexNamedBoolSum rest (fun environment =>
          family
            (boolTagUpdate
              (boolTagUpdate environment second secondValue)
              first firstValue)))) ?_
    exact rationalComplexBoolBind_congr (fun secondValue =>
      rationalComplexBoolBind_congr (fun firstValue =>
        rationalComplexNamedBoolSum_congr rest (fun environment => by
          rw [← boolTagUpdate_comm environment
            first second firstValue secondValue hne]
          exact rationalComplexEqv_refl _)))

/-- **Constructive named-binder permutation invariance.**  A structural
`List.Perm` witness transports any opaque rational-complex environment family
between the corresponding binder orders.  No decidable permutation search
or duplicate-freeness hypothesis is required. -/
theorem rationalComplexNamedBoolSum_perm
    {left right : List Nat} (hperm : left.Perm right)
    (family : (Nat → Bool) → RationalComplex) :
    RationalComplexEqv
      (rationalComplexNamedBoolSum left family)
      (rationalComplexNamedBoolSum right family) := by
  induction hperm generalizing family with
  | nil =>
      exact rationalComplexEqv_refl _
  | cons tag hperm ih =>
      simp only [rationalComplexNamedBoolSum]
      exact rationalComplexBoolBind_congr (fun value =>
        ih (fun environment =>
          family (boolTagUpdate environment tag value)))
  | swap first second rest =>
      exact rationalComplexEqv_symm
        (rationalComplexNamedBoolSum_swap first second rest family)
  | trans _ _ ihLeft ihRight =>
      exact rationalComplexEqv_trans
        (ihLeft family) (ihRight family)

/-! ## 4. Canonical range binders and list assignments -/

/-- Interpret a Boolean list as a total named environment whose first list
entry has name `start`.  Names below `start`, and names beyond the supplied
list, have the irrelevant default value `false`.

The definition is structural in both the offset and queried name.  In
particular, the range bridge below never computes a subtraction or constructs
the carrier of all Boolean assignments. -/
def boolListEnvironment : Nat → List Bool → Nat → Bool
  | 0, assignment, query => assignment.getD query false
  | _ + 1, _, 0 => false
  | start + 1, assignment, query + 1 =>
      boolListEnvironment start assignment query

/-- An empty list induces the constantly-false environment at every offset. -/
theorem boolListEnvironment_nil (start : Nat) :
    boolListEnvironment start [] = (fun _ => false) := by
  induction start with
  | zero =>
      funext query
      cases query <;> rfl
  | succ start ih =>
      funext query
      cases query with
      | zero => rfl
      | succ query => exact congrFun ih query

/-- At offset zero, the structural environment is ordinary `List.getD`. -/
theorem boolListEnvironment_zero (assignment : List Bool) :
    boolListEnvironment 0 assignment =
      (fun tag => assignment.getD tag false) := by
  rfl

/-- Prepending one list bit is exactly the same as updating the current named
coordinate and shifting the tail environment to the next name. -/
theorem boolListEnvironment_cons
    (start : Nat) (bit : Bool) (tail : List Bool) :
    boolListEnvironment start (bit :: tail) =
      boolTagUpdate
        (boolListEnvironment (start + 1) tail) start bit := by
  induction start with
  | zero =>
      funext query
      cases query <;>
        simp only [boolListEnvironment, boolTagUpdate,
          List.getD_cons_zero, List.getD_cons_succ,
          Nat.succ_ne_zero, ↓reduceIte]
  | succ start ih =>
      funext query
      cases query with
      | zero =>
          simp only [boolListEnvironment, boolTagUpdate,
            Nat.zero_ne_add_one, ↓reduceIte]
      | succ query =>
          simpa only [boolListEnvironment, boolTagUpdate,
            Nat.add_one_inj] using congrFun ih query

/-- A consecutive word of named binders is precisely the existing symbolic
Boolean-list sum at the same depth.  The proof is parametric in `depth`; it
uses only one-binder congruence and never unfolds a concrete binder tree. -/
theorem rationalComplexNamedBoolSum_range' :
    ∀ (start depth : Nat)
      (family : (Nat → Bool) → RationalComplex),
      RationalComplexEqv
        (rationalComplexNamedBoolSum (List.range' start depth) family)
        (rationalComplexBoolSum depth (fun assignment =>
          family (boolListEnvironment start assignment)))
  | start, 0, family => by
      simp only [List.range', rationalComplexNamedBoolSum,
        rationalComplexBoolSum]
      rw [boolListEnvironment_nil]
      exact rationalComplexEqv_refl _
  | start, depth + 1, family => by
      rw [List.range'_succ]
      simp only [rationalComplexNamedBoolSum, rationalComplexBoolBind,
        rationalComplexBoolSum]
      exact rationalComplexAdd_congr
        (rationalComplexEqv_trans
          (rationalComplexNamedBoolSum_range' (start + 1) depth
            (fun environment =>
              family (boolTagUpdate environment start false)))
          (rationalComplexBoolSum_congr depth (fun assignment => by
            rw [boolListEnvironment_cons]
            exact rationalComplexEqv_refl _)))
        (rationalComplexEqv_trans
          (rationalComplexNamedBoolSum_range' (start + 1) depth
            (fun environment =>
              family (boolTagUpdate environment start true)))
          (rationalComplexBoolSum_congr depth (fun assignment => by
            rw [boolListEnvironment_cons]
            exact rationalComplexEqv_refl _)))

/-- **Canonical named/list bridge.**  Binding names `0, ..., depth - 1` is
equivalent to the established symbolic Boolean sum whose assignment is read
with `List.getD`.  This is the representation bridge needed at cube depth
twenty four; the theorem itself remains wholly structural and opaque there. -/
theorem rationalComplexNamedBoolSum_range
    (depth : Nat) (family : (Nat → Bool) → RationalComplex) :
    RationalComplexEqv
      (rationalComplexNamedBoolSum (List.range depth) family)
      (rationalComplexBoolSum depth (fun assignment =>
        family (fun tag => assignment.getD tag false))) := by
  rw [List.range_eq_range']
  refine rationalComplexEqv_trans
    (rationalComplexNamedBoolSum_range' 0 depth family) ?_
  exact rationalComplexBoolSum_congr depth (fun assignment => by
    rw [boolListEnvironment_zero]
    exact rationalComplexEqv_refl _)

#print axioms boolTagUpdate_comm
#print axioms rationalComplexNamedBoolSum_congr
#print axioms rationalComplexNamedBoolSum_swap
#print axioms rationalComplexNamedBoolSum_perm
#print axioms boolListEnvironment_nil
#print axioms boolListEnvironment_cons
#print axioms rationalComplexNamedBoolSum_range'
#print axioms rationalComplexNamedBoolSum_range

end YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolSum
