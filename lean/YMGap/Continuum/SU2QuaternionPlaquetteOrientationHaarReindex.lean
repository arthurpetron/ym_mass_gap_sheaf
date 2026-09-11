/-
# Contextual reversal of a fundamental plaquette trace expansion

An outward elementary cube has three oppositely oriented faces.  At a fixed
four-index assignment, a reversed plaquette term is not the corresponding
standard term: complementing and reversing the cyclic indices also reverses
the four coefficient factors.  This leaf proves the exact constructive
repair after finite-product Haar:

* the four coefficient flip signs have cyclic product `+1`;
* the bounded Boolean change of variables is
  `(a,b,c,d) |-> (!a,!d,!c,!b)`;
* four factors may be reversed beneath arbitrary polynomial left and right
  context, but only after applying finite-product Haar; and
* consequently one reversed four-binder trace expansion may be replaced by
  the standard expansion inside an otherwise unresolved product.

Only sixteen fixed Boolean cases occur.  No assignment carrier is formed,
and no cube-sized Boolean recursion or raw polynomial commutativity is
unfolded.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexFourBoolFubini

namespace YMGap.Continuum.SU2QuaternionPlaquetteOrientationHaarReindex

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexFourBoolFubini

/-! ## 1. The exact four-sign audit -/

/-- The sign in
`F(row,column) = sign(row,column) R(!column,!row)`: diagonal coefficients
have sign `+1`, and off-diagonal coefficients have sign `-1`. -/
def fundamentalCoefficientFlipSign (row column : Bool) : Int :=
  if row = column then 1 else -1

/-- Around a closed four-index cycle, the coefficient-flip signs multiply to
`+1`.  This is the exact sign cancellation behind orientation reversal. -/
theorem fundamentalCoefficientFlipSign_cycle_four
    (a b c d : Bool) :
    (((fundamentalCoefficientFlipSign a b *
        fundamentalCoefficientFlipSign b c) *
      fundamentalCoefficientFlipSign c d) *
      fundamentalCoefficientFlipSign d a) = 1 := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- A reversed fixed summand is the reverse factor word of the standard
summand at the flipped cyclic assignment `(!a,!d,!c,!b)`.  The sixteen-case
kernel reduction simultaneously checks all four coefficient signs; the
preceding theorem records their invariant explicitly. -/
theorem reversedPlaquetteTraceTerm_eq_flippedStandard_reverseFactors
    (block0 block1 block2 block3 : Nat) (a b c d : Bool) :
    reversedPlaquetteTraceTerm block0 block1 block2 block3 a b c d =
      complexRatPolyMulFourLeft
        (reverseFundamentalCoefficient block1 (!b) (!a))
        (reverseFundamentalCoefficient block2 (!c) (!b))
        (forwardFundamentalCoefficient block3 (!d) (!c))
        (forwardFundamentalCoefficient block0 (!a) (!d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-! ## 2. Bounded Boolean change of variables -/

/-- Complementing one Boolean summation coordinate only exchanges its two
branches. -/
theorem rationalComplexBoolBind_complement
    (family : Bool -> RationalComplex) :
    RationalComplexEqv
      (rationalComplexBoolBind family)
      (rationalComplexBoolBind (fun index => family (!index))) := by
  simpa only [rationalComplexBoolBind, Bool.not_false, Bool.not_true] using
    (rationalComplexAdd_comm (family false) (family true))

/-- Simultaneously complement all four bounded Boolean binders. -/
theorem rationalComplexFourBoolSum_complement
    (family : Bool -> Bool -> Bool -> Bool -> RationalComplex) :
    RationalComplexEqv
      (rationalComplexFourBoolSum family)
      (rationalComplexFourBoolSum (fun a b c d =>
        family (!a) (!b) (!c) (!d))) := by
  unfold rationalComplexFourBoolSum
  refine rationalComplexEqv_trans
    (rationalComplexBoolBind_complement (fun a =>
      rationalComplexBoolBind (fun b =>
        rationalComplexBoolBind (fun c =>
          rationalComplexBoolBind (fun d => family a b c d))))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexBoolBind_congr (fun a =>
      rationalComplexBoolBind_complement (fun b =>
        rationalComplexBoolBind (fun c =>
          rationalComplexBoolBind (fun d => family (!a) b c d))))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexBoolBind_congr (fun a =>
      rationalComplexBoolBind_congr (fun b =>
        rationalComplexBoolBind_complement (fun c =>
          rationalComplexBoolBind (fun d => family (!a) (!b) c d))))) ?_
  exact rationalComplexBoolBind_congr (fun a =>
    rationalComplexBoolBind_congr (fun b =>
      rationalComplexBoolBind_congr (fun c =>
        rationalComplexBoolBind_complement (fun d =>
          family (!a) (!b) (!c) d))))

/-- The exact four-index reindexing used by plaquette orientation reversal.
Three constructive adjacent-binder exchanges reverse the last three
coordinates; the preceding involution complements all four. -/
theorem rationalComplexFourBoolSum_reverse_complement
    (family : Bool -> Bool -> Bool -> Bool -> RationalComplex) :
    RationalComplexEqv
      (rationalComplexFourBoolSum family)
      (rationalComplexFourBoolSum (fun a b c d =>
        family (!a) (!d) (!c) (!b))) := by
  have hperm : RationalComplexEqv
      (rationalComplexFourBoolSum family)
      (rationalComplexFourBoolSum (fun a b c d =>
        family a d c b)) := by
    unfold rationalComplexFourBoolSum
    apply rationalComplexBoolBind_congr
    intro a
    refine rationalComplexEqv_trans
      (rationalComplexBoolBind_swap (fun b c =>
        rationalComplexBoolBind (fun d => family a b c d))) ?_
    refine rationalComplexEqv_trans
      (rationalComplexBoolBind_congr (fun c =>
        rationalComplexBoolBind_swap (fun b d =>
          family a b c d))) ?_
    exact rationalComplexBoolBind_swap (fun c d =>
      rationalComplexBoolBind (fun b => family a b c d))
  exact rationalComplexEqv_trans hperm
    (rationalComplexFourBoolSum_complement (fun a b c d =>
      family a d c b))

/-! ## 3. Contextual reversal of exactly four polynomial factors -/

/-- Flatten one left-combed four-factor block beneath arbitrary left and
right polynomial context, only after finite-product Haar. -/
theorem finiteProductHaarComplex_mul_mulFourLeft_mul_eq_foldlFive
    (blockCount : Nat)
    (spectator first second third fourth suffix : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul
            (complexRatPolyMulFourLeft first second third fourth)
            suffix)))
      (finiteProductHaarComplex blockCount
        ([first, second, third, fourth, suffix].foldl
          complexRatPolyMul spectator)) := by
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_assoc_context blockCount spectator
      (complexRatPolyMulFourLeft first second third fourth) suffix) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_four_assoc blockCount spectator
      (complexRatPolyMul (complexRatPolyMul first second) third)
      fourth suffix) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_four_assoc blockCount spectator
      (complexRatPolyMul first second) third
      (complexRatPolyMul fourth suffix)) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_four_assoc blockCount spectator
      first second
      (complexRatPolyMul third (complexRatPolyMul fourth suffix))) ?_
  apply rationalComplexEqv_symm
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_assoc blockCount
      (complexRatPolyMul
        (complexRatPolyMul (complexRatPolyMul spectator first) second) third)
      fourth suffix) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_assoc blockCount
      (complexRatPolyMul (complexRatPolyMul spectator first) second)
      third (complexRatPolyMul fourth suffix)) ?_
  simpa only [List.foldl_cons, List.foldl_nil] using
    (finiteProductHaarComplex_mul_assoc blockCount
      (complexRatPolyMul spectator first) second
      (complexRatPolyMul third (complexRatPolyMul fourth suffix)))

/-- Reverse exactly four factors under arbitrary polynomial left and right
context.  The proof normalizes to a five-factor word, supplies the explicit
constructive permutation witness, and normalizes back. -/
theorem finiteProductHaarComplex_mul_mulFourLeft_reverse
    (blockCount : Nat)
    (spectator first second third fourth suffix : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul
            (complexRatPolyMulFourLeft first second third fourth)
            suffix)))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul
            (complexRatPolyMulFourLeft fourth third second first)
            suffix))) := by
  have hperm :
      [first, second, third, fourth, suffix].Perm
        [fourth, third, second, first, suffix] := by
    simpa using
      (((List.reverse_perm [first, second, third, fourth]).symm).append_right
        [suffix])
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_mulFourLeft_mul_eq_foldlFive
      blockCount spectator first second third fourth suffix) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_foldl_eq_mul_product blockCount spectator
      [first, second, third, fourth, suffix]) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_product_perm blockCount spectator hperm) ?_
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (finiteProductHaarComplex_foldl_eq_mul_product blockCount spectator
        [fourth, third, second, first, suffix])) ?_
  exact rationalComplexEqv_symm
    (finiteProductHaarComplex_mul_mulFourLeft_mul_eq_foldlFive
      blockCount spectator fourth third second first suffix)

/-! ## 4. One-face contextual orientation theorem -/

/-- At a fixed assignment, a reversed plaquette summand equals the standard
summand at the flipped cyclic assignment after contextual Haar evaluation.
The left and right polynomial contexts remain arbitrary. -/
theorem finiteProductHaarComplex_mul_reversedPlaquetteTraceTerm_eq_flippedStandard
    (blockCount : Nat) (spectator suffix : ComplexRatPoly)
    (block0 block1 block2 block3 : Nat) (a b c d : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul
            (reversedPlaquetteTraceTerm
              block0 block1 block2 block3 a b c d)
            suffix)))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul
            (standardPlaquetteTraceTerm
              block0 block1 block2 block3 (!a) (!d) (!c) (!b))
            suffix))) := by
  rw [reversedPlaquetteTraceTerm_eq_flippedStandard_reverseFactors]
  simpa only [standardPlaquetteTraceTerm] using
    (rationalComplexEqv_symm
      (finiteProductHaarComplex_mul_mulFourLeft_reverse
        blockCount spectator
        (forwardFundamentalCoefficient block0 (!a) (!d))
        (forwardFundamentalCoefficient block3 (!d) (!c))
        (reverseFundamentalCoefficient block2 (!c) (!b))
        (reverseFundamentalCoefficient block1 (!b) (!a))
        suffix))

/-- **Contextual one-face orientation fence.**  A reversed fundamental
plaquette trace expansion may be replaced by the standard expansion beneath
an arbitrary accumulated spectator and arbitrary unresolved suffix.  This
is the representative-level statement needed to standardize exactly the
three reversed faces of the elementary cube. -/
theorem finiteProductHaarComplex_mul_reversedPlaquetteTraceExpansion_eq_standard
    (blockCount : Nat) (spectator suffix : ComplexRatPoly)
    (block0 block1 block2 block3 : Nat) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul
            (reversedPlaquetteTraceExpansion block0 block1 block2 block3)
            suffix)))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul
            (standardPlaquetteTraceExpansion block0 block1 block2 block3)
            suffix))) := by
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_fourBoolSum_inner blockCount spectator suffix
      (reversedPlaquetteTraceTerm block0 block1 block2 block3)) ?_
  refine rationalComplexEqv_trans
    (rationalComplexFourBoolSum_congr (fun a b c d =>
      finiteProductHaarComplex_mul_reversedPlaquetteTraceTerm_eq_flippedStandard
        blockCount spectator suffix block0 block1 block2 block3 a b c d)) ?_
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (rationalComplexFourBoolSum_reverse_complement (fun a b c d =>
        finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyMul
              (standardPlaquetteTraceTerm
                block0 block1 block2 block3 a b c d)
              suffix))))) ?_
  exact rationalComplexEqv_symm
    (finiteProductHaarComplex_mul_fourBoolSum_inner blockCount spectator suffix
      (standardPlaquetteTraceTerm block0 block1 block2 block3))

#print axioms fundamentalCoefficientFlipSign_cycle_four
#print axioms reversedPlaquetteTraceTerm_eq_flippedStandard_reverseFactors
#print axioms rationalComplexBoolBind_complement
#print axioms rationalComplexFourBoolSum_complement
#print axioms rationalComplexFourBoolSum_reverse_complement
#print axioms finiteProductHaarComplex_mul_mulFourLeft_mul_eq_foldlFive
#print axioms finiteProductHaarComplex_mul_mulFourLeft_reverse
#print axioms finiteProductHaarComplex_mul_reversedPlaquetteTraceTerm_eq_flippedStandard
#print axioms finiteProductHaarComplex_mul_reversedPlaquetteTraceExpansion_eq_standard

end YMGap.Continuum.SU2QuaternionPlaquetteOrientationHaarReindex
