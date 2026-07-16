/-
# Finite cylinder quadratic stability

This module turns a uniform error bound for finitely many joint cylinder
values into an explicit error bound for the associated finite reflection
quadratic.  It is deliberately independent of the particular cylinder
carrier.  A later physical bridge must still identify its finite joint law
with the corrected-slab law; no such identification is assumed here.

For coefficients `c_i`, the resulting modulus is

    (sum_i |c_i|) * (sum_i |c_i|) * epsilon.

All sums and bounds are exact in `Q'`.
-/

import YMGap.Constructive.CRealExp
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.Z4FiniteCylinderQuadraticStability

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS

local infix:50 " ≈ " => Q'.eqv

/-! ## Exact finite-sum inequalities -/

/-- Abelian regrouping `(a + a') - (b + b') ≃ (a - b) + (a' - b')`. -/
private theorem sub_add_rearrange (a a' b b' : Q') :
    ((a + a') + (-(b + b'))) ≈
      ((a + (-b)) + (a' + (-b'))) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (a + a') _ _ (Q'.neg_add_eqv b b')) ?_
  exact Q'.add_swap_inner a a' (-b) (-b')

/-- Triangle inequality for the difference of two exact finite list sums. -/
theorem abs_listQSum_sub_le {A : Type} (left right : A → Q') :
    ∀ xs : List A,
      Q'.abs (listQSum left xs + (-listQSum right xs)) ≤
        listQSum (fun x => Q'.abs (left x + (-right x))) xs
  | [] => by
      change Q'.abs ((0 : Q') + (-(0 : Q'))) ≤ (0 : Q')
      decide
  | x :: xs => by
      have hrearrange := sub_add_rearrange
        (left x) (listQSum left xs) (right x) (listQSum right xs)
      have htriangle := abs_add_le
        (left x + (-right x))
        (listQSum left xs + (-listQSum right xs))
      have htail := abs_listQSum_sub_le left right xs
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (abs_eqv_congr hrearrange)) ?_
      exact Q'.le_trans' _ _ _ htriangle
        (Q'.add_le_add_left _ _ _ htail)

/-- Pointwise comparison passes through an exact finite list sum. -/
theorem listQSum_mono {A : Type} (lower upper : A → Q') :
    ∀ xs : List A,
      (∀ x, x ∈ xs → lower x ≤ upper x) →
      listQSum lower xs ≤ listQSum upper xs
  | [], _ => Q'.le_refl' 0
  | x :: xs, h =>
      Q'.add_le_add
        (h x List.mem_cons_self)
        (listQSum_mono lower upper xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- A common scalar turns an absolute difference bound into a scaled bound. -/
theorem abs_common_mul_sub_le
    (coefficient left right epsilon : Q')
    (herror : Q'.abs (left + (-right)) ≤ epsilon) :
    Q'.abs
        (coefficient * left + (-(coefficient * right))) ≤
      Q'.abs coefficient * epsilon := by
  have hfactor :
      (coefficient * left + (-(coefficient * right))) ≈
        coefficient * (left + (-right)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (coefficient * left) _ _
        (Q'.eqv_symm (Q'.mul_neg_eqv coefficient right))) ?_
    exact Q'.eqv_symm (Q'.mul_add_eqv coefficient left (-right))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (abs_eqv_congr hfactor)) ?_
  refine Q'.le_trans' _ _ _
    (abs_mul_le coefficient (left + (-right))) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ herror
    (Q'.abs_nonneg coefficient)

/-! ## Finite reflection quadratics and their coefficient norm -/

/-- A finite quadratic assembled from a joint law. -/
def finiteJointQuadratic {State : Type}
    (states : List State) (coefficient : State → Q')
    (joint : State → State → Q') : Q' :=
  listQSum
    (fun left => listQSum
      (fun right =>
        (coefficient left * coefficient right) * joint left right)
      states)
    states

/-- Exact `l¹` norm of a finite coefficient list. -/
def coefficientL1 {State : Type}
    (states : List State) (coefficient : State → Q') : Q' :=
  listQSum (fun state => Q'.abs (coefficient state)) states

/-- Literal double-list coefficient norm before factorization. -/
def coefficientPairL1 {State : Type}
    (states : List State) (coefficient : State → Q') : Q' :=
  listQSum
    (fun left => listQSum
      (fun right => Q'.abs (coefficient left * coefficient right))
      states)
    states

/-- The literal pair norm is bounded by the square of the coefficient `l¹` norm. -/
theorem coefficientPairL1_le_square {State : Type}
    (states : List State) (coefficient : State → Q') :
    coefficientPairL1 states coefficient ≤
      coefficientL1 states coefficient * coefficientL1 states coefficient := by
  have hpointwise :
      coefficientPairL1 states coefficient ≤
        listQSum
          (fun left => listQSum
            (fun right =>
              Q'.abs (coefficient left) * Q'.abs (coefficient right))
            states)
          states := by
    unfold coefficientPairL1
    apply listQSum_mono
    intro left hleft
    apply listQSum_mono
    intro right hright
    exact abs_mul_le (coefficient left) (coefficient right)
  refine Q'.le_trans' _ _ _ hpointwise ?_
  exact Q'.le_of_eqv
    (listQSum_product
      (fun state => Q'.abs (coefficient state))
      (fun state => Q'.abs (coefficient state))
      states states)

/-! ## Event-error to Gram-error transfer -/

/-- A uniform pointwise joint-law error controls the finite quadratic by the
literal double-list coefficient norm. -/
theorem finiteJointQuadratic_abs_sub_le_pairL1
    {State : Type}
    (states : List State) (coefficient : State → Q')
    (leftLaw rightLaw : State → State → Q')
    (epsilon : Q')
    (herror : ∀ left right, left ∈ states → right ∈ states →
      Q'.abs (leftLaw left right + (-rightLaw left right)) ≤ epsilon) :
    Q'.abs
        (finiteJointQuadratic states coefficient leftLaw +
          (-finiteJointQuadratic states coefficient rightLaw)) ≤
      coefficientPairL1 states coefficient * epsilon := by
  let leftRow : State → Q' := fun left =>
    listQSum
      (fun right =>
        (coefficient left * coefficient right) * leftLaw left right)
      states
  let rightRow : State → Q' := fun left =>
    listQSum
      (fun right =>
        (coefficient left * coefficient right) * rightLaw left right)
      states
  have houter := abs_listQSum_sub_le leftRow rightRow states
  have hrows :
      listQSum (fun left => Q'.abs (leftRow left + (-rightRow left))) states ≤
        listQSum
          (fun left => listQSum
            (fun right => Q'.abs (coefficient left * coefficient right))
            states * epsilon)
          states := by
    apply listQSum_mono
    intro left hleft
    have hinner := abs_listQSum_sub_le
      (fun right =>
        (coefficient left * coefficient right) * leftLaw left right)
      (fun right =>
        (coefficient left * coefficient right) * rightLaw left right)
      states
    refine Q'.le_trans' _ _ _ hinner ?_
    have hterms :
        listQSum
            (fun right => Q'.abs
              ((coefficient left * coefficient right) * leftLaw left right +
                (-((coefficient left * coefficient right) * rightLaw left right))))
            states ≤
          listQSum
            (fun right =>
              Q'.abs (coefficient left * coefficient right) * epsilon)
            states := by
      apply listQSum_mono
      intro right hright
      exact abs_common_mul_sub_le
        (coefficient left * coefficient right)
        (leftLaw left right) (rightLaw left right) epsilon
        (herror left right hleft hright)
    refine Q'.le_trans' _ _ _ hterms ?_
    exact Q'.le_of_eqv
      (listQSum_mul_right
        (fun right => Q'.abs (coefficient left * coefficient right))
        epsilon states)
  unfold finiteJointQuadratic
  change Q'.abs (listQSum leftRow states + (-listQSum rightRow states)) ≤ _
  refine Q'.le_trans' _ _ _ houter (Q'.le_trans' _ _ _ hrows ?_)
  exact Q'.le_of_eqv
    (listQSum_mul_right
      (fun left => listQSum
        (fun right => Q'.abs (coefficient left * coefficient right))
        states)
      epsilon states)

/-- The same stability estimate in the factored square-norm form used by a
finite reflection-polynomial convergence modulus. -/
theorem finiteJointQuadratic_abs_sub_le_square
    {State : Type}
    (states : List State) (coefficient : State → Q')
    (leftLaw rightLaw : State → State → Q')
    (epsilon : Q') (hepsilon : (0 : Q') ≤ epsilon)
    (herror : ∀ left right, left ∈ states → right ∈ states →
      Q'.abs (leftLaw left right + (-rightLaw left right)) ≤ epsilon) :
    Q'.abs
        (finiteJointQuadratic states coefficient leftLaw +
          (-finiteJointQuadratic states coefficient rightLaw)) ≤
      (coefficientL1 states coefficient * coefficientL1 states coefficient) *
        epsilon := by
  refine Q'.le_trans' _ _ _
    (finiteJointQuadratic_abs_sub_le_pairL1
      states coefficient leftLaw rightLaw epsilon herror) ?_
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (coefficientPairL1_le_square states coefficient) hepsilon

/-- Positivity of a reference quadratic and an absolute comparison modulus
give the expected approximate positivity of the compared quadratic. -/
theorem ge_neg_of_reference_nonnegative
    {value reference modulus : Q'}
    (href : (0 : Q') ≤ reference)
    (hclose : Q'.abs (value + (-reference)) ≤ modulus) :
    -modulus ≤ value := by
  have hneg : -modulus ≤ value + (-reference) :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hclose)
      (neg_abs_le (value + (-reference)))
  have hadd : (0 : Q') + (-modulus) ≤
      reference + (value + (-reference)) :=
    Q'.add_le_add href hneg
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (-modulus)))) ?_
  refine Q'.le_trans' _ _ _ hadd ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv reference value (-reference))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (reference + value) (value + reference) (-reference)
      (Q'.add_comm_eqv reference value)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv value reference (-reference)) ?_
  have hcancel : (reference + (-reference)) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv reference (-reference))
      (Q'.neg_add_self_eqv reference)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left value _ _ hcancel) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' value)

/-- Constructive approximate reflection positivity: if the reference finite
joint law is reflection positive and every joint value is epsilon-close, the
compared quadratic is bounded below by the explicit square-norm modulus. -/
theorem finiteJointQuadratic_ge_neg_square_modulus
    {State : Type}
    (states : List State) (coefficient : State → Q')
    (comparedLaw referenceLaw : State → State → Q')
    (epsilon : Q') (hepsilon : (0 : Q') ≤ epsilon)
    (hreference : (0 : Q') ≤
      finiteJointQuadratic states coefficient referenceLaw)
    (herror : ∀ left right, left ∈ states → right ∈ states →
      Q'.abs (comparedLaw left right + (-referenceLaw left right)) ≤ epsilon) :
    -((coefficientL1 states coefficient * coefficientL1 states coefficient) *
        epsilon) ≤
      finiteJointQuadratic states coefficient comparedLaw := by
  exact ge_neg_of_reference_nonnegative hreference
    (finiteJointQuadratic_abs_sub_le_square
      states coefficient comparedLaw referenceLaw epsilon hepsilon herror)

#print axioms abs_listQSum_sub_le
#print axioms listQSum_mono
#print axioms abs_common_mul_sub_le
#print axioms coefficientPairL1_le_square
#print axioms finiteJointQuadratic_abs_sub_le_pairL1
#print axioms finiteJointQuadratic_abs_sub_le_square
#print axioms ge_neg_of_reference_nonnegative
#print axioms finiteJointQuadratic_ge_neg_square_modulus

end YMGap.Continuum.Z4FiniteCylinderQuadraticStability
