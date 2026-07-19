/-
# Symbolic Boolean sums for honest complex rational polynomials

Finite trace expansions require repeated sums over Boolean matrix indices.
Materializing the complete assignment carrier is harmless at depth four but
catastrophic at the twenty-four-index cube boundary.  This leaf therefore
defines a structurally recursive sum which consumes a function on Boolean
lists without ever constructing the list of all assignments.

This is a representation fence, not a claim of subexponential evaluation:
unfolding, simplifying, reducing, or evaluating the recursion at depth
twenty four would still expose `2^24` leaves.  Cube-wide proofs must keep the
sum opaque and use only the abstract congruence, linearity, evaluation, and
Haar-commutation theorems below.  Concrete unfolding is reserved for the
safe four-index face and three-index vertex identities.

At depth `n`, the function is evaluated only on lists of length `n`.  The
false branch is added before the true branch, and the complete addition tree
is retained literally.  Evaluation and finite-product Haar commute with this
symbolic sum by induction from their one-step addition laws.

The rational-complex ring identities below are value-level setoid theorems.
They may reorganize an evaluated trace expression, but they do not imply raw
`RatPoly` equality, raw polynomial reordering, Haar extensionality, or Haar
multiplicativity.

No assignment carrier or list of all assignments, face product, cube
product, density polynomial, bounded labelling family, or trajectory is
unfolded or materialized here.  Individual branch-prefix lists occur only
inside the structural recursion.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra

namespace YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;>
             ac_rfl))

/-! ## 1. One-binder and recursive Boolean sums -/

/-- Sum one Boolean-indexed rational-complex family, false branch first. -/
def rationalComplexBoolBind
    (family : Bool → RationalComplex) : RationalComplex :=
  rationalComplexAdd (family false) (family true)

/-- Sum one Boolean-indexed honest complex-polynomial family, false branch
first. -/
def complexRatPolyBoolBind
    (family : Bool → ComplexRatPoly) : ComplexRatPoly :=
  complexRatPolyAdd (family false) (family true)

/-- Structurally sum a rational-complex function over all Boolean lists of
the requested length, without constructing the assignment carrier. -/
def rationalComplexBoolSum :
    (depth : Nat) → (List Bool → RationalComplex) → RationalComplex
  | 0, family => family []
  | depth + 1, family =>
      rationalComplexAdd
        (rationalComplexBoolSum depth
          (fun assignment => family (false :: assignment)))
        (rationalComplexBoolSum depth
          (fun assignment => family (true :: assignment)))

/-- Polynomial analogue of `rationalComplexBoolSum`.  This preserves the
literal false-before-true addition tree. -/
def complexRatPolyBoolSum :
    (depth : Nat) → (List Bool → ComplexRatPoly) → ComplexRatPoly
  | 0, family => family []
  | depth + 1, family =>
      complexRatPolyAdd
        (complexRatPolyBoolSum depth
          (fun assignment => family (false :: assignment)))
        (complexRatPolyBoolSum depth
          (fun assignment => family (true :: assignment)))

theorem rationalComplexBoolSum_zero
    (family : List Bool → RationalComplex) :
    rationalComplexBoolSum 0 family = family [] := rfl

theorem rationalComplexBoolSum_succ
    (depth : Nat) (family : List Bool → RationalComplex) :
    rationalComplexBoolSum (depth + 1) family =
      rationalComplexAdd
        (rationalComplexBoolSum depth
          (fun assignment => family (false :: assignment)))
        (rationalComplexBoolSum depth
          (fun assignment => family (true :: assignment))) := rfl

theorem complexRatPolyBoolSum_zero
    (family : List Bool → ComplexRatPoly) :
    complexRatPolyBoolSum 0 family = family [] := rfl

theorem complexRatPolyBoolSum_succ
    (depth : Nat) (family : List Bool → ComplexRatPoly) :
    complexRatPolyBoolSum (depth + 1) family =
      complexRatPolyAdd
        (complexRatPolyBoolSum depth
          (fun assignment => family (false :: assignment)))
        (complexRatPolyBoolSum depth
          (fun assignment => family (true :: assignment))) := rfl

/-! ## 2. Rational-complex value algebra -/

theorem rationalComplexAdd_assoc
    (first second third : RationalComplex) :
    RationalComplexEqv
      (rationalComplexAdd (rationalComplexAdd first second) third)
      (rationalComplexAdd first (rationalComplexAdd second third)) :=
  ⟨Q'.add_assoc_eqv first.1 second.1 third.1,
    Q'.add_assoc_eqv first.2 second.2 third.2⟩

theorem rationalComplexAdd_comm
    (left right : RationalComplex) :
    RationalComplexEqv
      (rationalComplexAdd left right)
      (rationalComplexAdd right left) :=
  ⟨Q'.add_comm_eqv left.1 right.1,
    Q'.add_comm_eqv left.2 right.2⟩

/-- Exchange the two inner summands while preserving the outer binary
addition tree. -/
theorem rationalComplexAdd_swap_inner
    (a b c d : RationalComplex) :
    RationalComplexEqv
      (rationalComplexAdd
        (rationalComplexAdd a b) (rationalComplexAdd c d))
      (rationalComplexAdd
        (rationalComplexAdd a c) (rationalComplexAdd b d)) :=
  ⟨Q'.add_swap_inner a.1 b.1 c.1 d.1,
    Q'.add_swap_inner a.2 b.2 c.2 d.2⟩

theorem rationalComplexMul_assoc
    (first second third : RationalComplex) :
    RationalComplexEqv
      (rationalComplexMul (rationalComplexMul first second) third)
      (rationalComplexMul first (rationalComplexMul second third)) := by
  unfold rationalComplexMul RationalComplexEqv
  constructor <;> ring_qeqv

theorem rationalComplexMul_comm
    (left right : RationalComplex) :
    RationalComplexEqv
      (rationalComplexMul left right)
      (rationalComplexMul right left) := by
  unfold rationalComplexMul RationalComplexEqv
  constructor <;> ring_qeqv

theorem rationalComplexMul_add
    (factor left right : RationalComplex) :
    RationalComplexEqv
      (rationalComplexMul factor (rationalComplexAdd left right))
      (rationalComplexAdd
        (rationalComplexMul factor left)
        (rationalComplexMul factor right)) := by
  unfold rationalComplexMul rationalComplexAdd RationalComplexEqv
  constructor <;> ring_qeqv

theorem rationalComplexAdd_mul
    (left right factor : RationalComplex) :
    RationalComplexEqv
      (rationalComplexMul (rationalComplexAdd left right) factor)
      (rationalComplexAdd
        (rationalComplexMul left factor)
        (rationalComplexMul right factor)) := by
  unfold rationalComplexMul rationalComplexAdd RationalComplexEqv
  constructor <;> ring_qeqv

/-- The two possible orders of two nested Boolean binders agree at evaluated
rational-complex value level. -/
theorem rationalComplexBoolBind_swap
    (family : Bool → Bool → RationalComplex) :
    RationalComplexEqv
      (rationalComplexBoolBind
        (fun first => rationalComplexBoolBind (family first)))
      (rationalComplexBoolBind
        (fun second => rationalComplexBoolBind
          (fun first => family first second))) := by
  unfold rationalComplexBoolBind
  exact rationalComplexAdd_swap_inner
    (family false false) (family false true)
    (family true false) (family true true)

/-- One Boolean binder respects pointwise rational-complex equivalence. -/
theorem rationalComplexBoolBind_congr
    {left right : Bool → RationalComplex}
    (hpointwise : ∀ index,
      RationalComplexEqv (left index) (right index)) :
    RationalComplexEqv
      (rationalComplexBoolBind left)
      (rationalComplexBoolBind right) := by
  unfold rationalComplexBoolBind
  exact rationalComplexAdd_congr
    (hpointwise false) (hpointwise true)

/-- Left multiplication distributes through one Boolean binder. -/
theorem rationalComplexMul_boolBind
    (factor : RationalComplex)
    (family : Bool → RationalComplex) :
    RationalComplexEqv
      (rationalComplexMul factor
        (rationalComplexBoolBind family))
      (rationalComplexBoolBind
        (fun index => rationalComplexMul factor (family index))) := by
  unfold rationalComplexBoolBind
  exact rationalComplexMul_add factor (family false) (family true)

/-- Right multiplication distributes through one Boolean binder. -/
theorem rationalComplexBoolBind_mul
    (family : Bool → RationalComplex)
    (factor : RationalComplex) :
    RationalComplexEqv
      (rationalComplexMul
        (rationalComplexBoolBind family) factor)
      (rationalComplexBoolBind
        (fun index => rationalComplexMul (family index) factor)) := by
  unfold rationalComplexBoolBind
  exact rationalComplexAdd_mul (family false) (family true) factor

/-! ## 3. Congruence and linearity of the recursive value sum -/

theorem rationalComplexBoolSum_congr
    (depth : Nat)
    {left right : List Bool → RationalComplex}
    (hpointwise : ∀ assignment,
      RationalComplexEqv (left assignment) (right assignment)) :
    RationalComplexEqv
      (rationalComplexBoolSum depth left)
      (rationalComplexBoolSum depth right) := by
  induction depth generalizing left right with
  | zero => exact hpointwise []
  | succ depth ih =>
      exact rationalComplexAdd_congr
        (ih
          (left := fun assignment => left (false :: assignment))
          (right := fun assignment => right (false :: assignment))
          (fun assignment => hpointwise (false :: assignment)))
        (ih
          (left := fun assignment => left (true :: assignment))
          (right := fun assignment => right (true :: assignment))
          (fun assignment => hpointwise (true :: assignment)))

theorem rationalComplexBoolSum_add
    (depth : Nat) (left right : List Bool → RationalComplex) :
    RationalComplexEqv
      (rationalComplexBoolSum depth
        (fun assignment =>
          rationalComplexAdd (left assignment) (right assignment)))
      (rationalComplexAdd
        (rationalComplexBoolSum depth left)
        (rationalComplexBoolSum depth right)) := by
  induction depth generalizing left right with
  | zero => exact rationalComplexEqv_refl _
  | succ depth ih =>
      exact rationalComplexEqv_trans
        (rationalComplexAdd_congr
          (ih
            (fun assignment => left (false :: assignment))
            (fun assignment => right (false :: assignment)))
          (ih
            (fun assignment => left (true :: assignment))
            (fun assignment => right (true :: assignment))))
        (rationalComplexAdd_swap_inner _ _ _ _)

theorem rationalComplexMul_boolSum
    (factor : RationalComplex) :
    ∀ (depth : Nat) (family : List Bool → RationalComplex),
      RationalComplexEqv
        (rationalComplexMul factor
          (rationalComplexBoolSum depth family))
        (rationalComplexBoolSum depth
          (fun assignment =>
            rationalComplexMul factor (family assignment)))
  | 0, _ => rationalComplexEqv_refl _
  | depth + 1, family =>
      rationalComplexEqv_trans
        (rationalComplexMul_add factor _ _)
        (rationalComplexAdd_congr
          (rationalComplexMul_boolSum factor depth
            (fun assignment => family (false :: assignment)))
          (rationalComplexMul_boolSum factor depth
            (fun assignment => family (true :: assignment))))

theorem rationalComplexBoolSum_mul
    (factor : RationalComplex) :
    ∀ (depth : Nat) (family : List Bool → RationalComplex),
      RationalComplexEqv
        (rationalComplexMul
          (rationalComplexBoolSum depth family) factor)
        (rationalComplexBoolSum depth
          (fun assignment =>
            rationalComplexMul (family assignment) factor))
  | 0, _ => rationalComplexEqv_refl _
  | depth + 1, family =>
      rationalComplexEqv_trans
        (rationalComplexAdd_mul _ _ factor)
        (rationalComplexAdd_congr
          (rationalComplexBoolSum_mul factor depth
            (fun assignment => family (false :: assignment)))
          (rationalComplexBoolSum_mul factor depth
            (fun assignment => family (true :: assignment))))

/-! ## 4. Evaluation and Haar commute with symbolic Boolean sums -/

theorem evalComplexRatPoly_boolBind
    (rho : Nat → Q') (family : Bool → ComplexRatPoly) :
    RationalComplexEqv
      (evalComplexRatPoly rho (complexRatPolyBoolBind family))
      (rationalComplexBoolBind
        (fun index => evalComplexRatPoly rho (family index))) := by
  unfold complexRatPolyBoolBind rationalComplexBoolBind
  exact evalComplexRatPoly_add rho (family false) (family true)

theorem finiteProductHaarComplex_boolBind
    (blockCount : Nat) (family : Bool → ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyBoolBind family))
      (rationalComplexBoolBind
        (fun index => finiteProductHaarComplex blockCount (family index))) := by
  unfold complexRatPolyBoolBind rationalComplexBoolBind
  exact finiteProductHaarComplex_add blockCount (family false) (family true)

theorem evalComplexRatPoly_boolSum
    (rho : Nat → Q') :
    ∀ (depth : Nat) (family : List Bool → ComplexRatPoly),
      RationalComplexEqv
        (evalComplexRatPoly rho
          (complexRatPolyBoolSum depth family))
        (rationalComplexBoolSum depth
          (fun assignment =>
            evalComplexRatPoly rho (family assignment)))
  | 0, _ => rationalComplexEqv_refl _
  | depth + 1, family =>
      rationalComplexEqv_trans
        (evalComplexRatPoly_add rho _ _)
        (rationalComplexAdd_congr
          (evalComplexRatPoly_boolSum rho depth
            (fun assignment => family (false :: assignment)))
          (evalComplexRatPoly_boolSum rho depth
            (fun assignment => family (true :: assignment))))

theorem finiteProductHaarComplex_boolSum
    (blockCount : Nat) :
    ∀ (depth : Nat) (family : List Bool → ComplexRatPoly),
      RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyBoolSum depth family))
        (rationalComplexBoolSum depth
          (fun assignment =>
            finiteProductHaarComplex blockCount (family assignment)))
  | 0, _ => rationalComplexEqv_refl _
  | depth + 1, family =>
      rationalComplexEqv_trans
        (finiteProductHaarComplex_add blockCount _ _)
        (rationalComplexAdd_congr
          (finiteProductHaarComplex_boolSum blockCount depth
            (fun assignment => family (false :: assignment)))
          (finiteProductHaarComplex_boolSum blockCount depth
            (fun assignment => family (true :: assignment))))

#print axioms rationalComplexMul_assoc
#print axioms rationalComplexMul_comm
#print axioms rationalComplexMul_add
#print axioms rationalComplexAdd_mul
#print axioms rationalComplexBoolBind_swap
#print axioms rationalComplexBoolBind_congr
#print axioms rationalComplexMul_boolBind
#print axioms rationalComplexBoolBind_mul
#print axioms rationalComplexBoolSum_congr
#print axioms rationalComplexBoolSum_add
#print axioms rationalComplexMul_boolSum
#print axioms rationalComplexBoolSum_mul
#print axioms evalComplexRatPoly_boolSum
#print axioms finiteProductHaarComplex_boolSum

end YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra
