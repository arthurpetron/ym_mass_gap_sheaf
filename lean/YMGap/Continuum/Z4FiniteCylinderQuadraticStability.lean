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

/-! ## Upper-side perturbation compiler -/

/-- An absolute difference bound gives the corresponding upper comparison.
This is the one-sided companion to `ge_neg_of_reference_nonnegative`: it is
the exact algebraic step needed when a physical law is only approximately
identified with a reference law. -/
theorem le_reference_add_of_abs_sub_le
    {value reference modulus : Q'}
    (hclose : Q'.abs (value + (-reference)) ≤ modulus) :
    value ≤ reference + modulus := by
  have hdiff : value + (-reference) ≤ modulus :=
    Q'.le_trans' _ _ _
      (Q'.le_abs_self (value + (-reference))) hclose
  have hadd :
      (value + (-reference)) + reference ≤ modulus + reference :=
    Q'.add_le_add_right
      (value + (-reference)) modulus reference hdiff
  have hleft :
      (value + (-reference)) + reference ≈ value := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv value (-reference) reference) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left value ((-reference) + reference) 0
        (Q'.neg_add_self_eqv reference)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' value)
  have hright : modulus + reference ≈ reference + modulus :=
    Q'.add_comm_eqv modulus reference
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright))

/-- A strict reference quadratic estimate and an absolute law-comparison
error combine into a rate with the error added explicitly.  No positivity or
completion hypothesis is hidden here; callers must provide the reference
bound and the actual coefficient norm. -/
theorem upper_rate_of_reference_gap_and_abs_error
    {value reference norm rate error : Q'}
    (hreference : reference ≤ rate * norm)
    (herror : Q'.abs (value + (-reference)) ≤ error * norm) :
    value ≤ (rate + error) * norm := by
  have hadd := le_reference_add_of_abs_sub_le herror
  have hrate : reference + error * norm ≤ rate * norm + error * norm :=
    Q'.add_le_add_right reference (rate * norm) (error * norm) hreference
  refine Q'.le_trans' _ _ _ hadd (Q'.le_trans' _ _ _ hrate ?_)
  exact Q'.le_of_eqv (Q'.eqv_symm (Q'.add_mul_eqv rate error norm))

/-- Finite-cylinder specialization of the perturbation compiler.  A common
entrywise error `epsilon` changes a reference strict rate only by the
coefficient `l^1` square times `epsilon`. -/
theorem finiteJointQuadratic_le_reference_rate_add_error
    {State : Type}
    (states : List State) (coefficient : State → Q')
    (comparedLaw referenceLaw : State → State → Q')
    (epsilon rate : Q') (hepsilon : (0 : Q') ≤ epsilon)
    (hreference :
      finiteJointQuadratic states coefficient referenceLaw ≤
        rate * (coefficientL1 states coefficient * coefficientL1 states coefficient))
    (herror : ∀ left right, left ∈ states → right ∈ states →
      Q'.abs (comparedLaw left right + (-referenceLaw left right)) ≤ epsilon) :
    finiteJointQuadratic states coefficient comparedLaw ≤
      (rate + epsilon) *
        (coefficientL1 states coefficient * coefficientL1 states coefficient) := by
  have hfinite := finiteJointQuadratic_abs_sub_le_square
    states coefficient comparedLaw referenceLaw epsilon hepsilon herror
  have hfinite' :
      Q'.abs
          (finiteJointQuadratic states coefficient comparedLaw +
            (-finiteJointQuadratic states coefficient referenceLaw)) ≤
        epsilon *
          (coefficientL1 states coefficient * coefficientL1 states coefficient) :=
    Q'.le_trans' _ _ _ hfinite
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv
          (coefficientL1 states coefficient * coefficientL1 states coefficient)
          epsilon))
  exact upper_rate_of_reference_gap_and_abs_error
    hreference
    hfinite'

private theorem lt_of_lt_of_le_local {a b c : Q'}
    (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hbd : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
  have hcd : (0 : Int) < (c.den : Int) := by exact_mod_cast c.den_pos
  have had : (0 : Int) ≤ (a.den : Int) := by exact_mod_cast Nat.zero_le _
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have h := Int.mul_lt_mul_of_pos_right e1 hcd
    have hr : (a.num * (b.den : Int)) * (c.den : Int) =
        (a.num * (c.den : Int)) * (b.den : Int) := by
      ac_rfl
    rwa [hr] at h
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    have h := Int.mul_le_mul_of_nonneg_right e2 had
    have hl : (b.num * (c.den : Int)) * (a.den : Int) =
        (b.num * (a.den : Int)) * (c.den : Int) := by
      ac_rfl
    have hr : (c.num * (b.den : Int)) * (a.den : Int) =
        (c.num * (a.den : Int)) * (b.den : Int) := by
      ac_rfl
    rwa [hl, hr] at h
  have schain : (a.num * (c.den : Int)) * (b.den : Int)
          < (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_lt_of_le s1 s2
  exact Int.lt_of_mul_lt_mul_right schain (by exact_mod_cast Nat.zero_le _)

private theorem mul_lt_mul_of_pos_right_local {a b c : Q'}
    (hc : (0 : Q') < c) (hab : a < b) : a * c < b * c := by
  have hleft : a * c < c * b :=
    Q'.lt_of_le_of_lt
      (Q'.le_of_eqv (Q'.mul_comm_eqv a c))
      (Q'.mul_lt_mul_of_pos_left hc hab)
  exact lt_of_lt_of_le_local hleft
    (Q'.le_of_eqv (Q'.mul_comm_eqv c b))

/-- If the accumulated reference rate plus explicit comparison error remains
strictly below one, the same compiler produces a strict finite quadratic
bound on every coefficient vector with positive `l^1` mass. -/
theorem finiteJointQuadratic_lt_square_of_reference_rate_and_abs_error
    {State : Type}
    (states : List State) (coefficient : State → Q')
    (comparedLaw referenceLaw : State → State → Q')
    (epsilon rate : Q') (hepsilon : (0 : Q') ≤ epsilon)
    (hreference :
      finiteJointQuadratic states coefficient referenceLaw ≤
        rate * (coefficientL1 states coefficient * coefficientL1 states coefficient))
    (herror : ∀ left right, left ∈ states → right ∈ states →
      Q'.abs (comparedLaw left right + (-referenceLaw left right)) ≤ epsilon)
    (hstrict : rate + epsilon < (1 : Q'))
    (hcoefficient : (0 : Q') < coefficientL1 states coefficient) :
    finiteJointQuadratic states coefficient comparedLaw <
      coefficientL1 states coefficient * coefficientL1 states coefficient := by
  have hupper := finiteJointQuadratic_le_reference_rate_add_error
    states coefficient comparedLaw referenceLaw epsilon rate hepsilon
      hreference herror
  let norm := coefficientL1 states coefficient * coefficientL1 states coefficient
  have hnorm : (0 : Q') < norm := Q'.mul_pos hcoefficient hcoefficient
  have hscaled : (rate + epsilon) * norm < (1 : Q') * norm :=
    mul_lt_mul_of_pos_right_local hnorm hstrict
  have hscaled' : (rate + epsilon) * norm < norm :=
    lt_of_lt_of_le_local hscaled (Q'.le_of_eqv (Q'.one_mul_eqv norm))
  exact Q'.lt_of_le_of_lt hupper hscaled'

/-! ## Direct strictness consumers for an already-built absolute gap -/

/-- An absolute rate bound becomes strict as soon as its comparison norm is
positive.  This scalar form is deliberately independent of the finite
carrier presentation, so physical diagonal forms can consume it directly. -/
theorem abs_lt_of_abs_le_rate_mul_of_pos_norm
    {value norm rate : Q'}
    (hgap : Q'.abs value ≤ rate * norm)
    (hstrict : rate < (1 : Q'))
    (hnorm : (0 : Q') < norm) :
    Q'.abs value < norm := by
  have hscaled : rate * norm < (1 : Q') * norm :=
    mul_lt_mul_of_pos_right_local hnorm hstrict
  have hscaled' : rate * norm < norm :=
    lt_of_lt_of_le_local hscaled (Q'.le_of_eqv (Q'.one_mul_eqv norm))
  exact Q'.lt_of_le_of_lt hgap hscaled'

/-- The signed quadratic itself is strictly below the same positive norm. -/
theorem lt_of_abs_le_rate_mul_of_pos_norm
    {value norm rate : Q'}
    (hgap : Q'.abs value ≤ rate * norm)
    (hstrict : rate < (1 : Q'))
    (hnorm : (0 : Q') < norm) :
    value < norm := by
  exact Q'.lt_of_le_of_lt (Q'.le_abs_self _)
    (abs_lt_of_abs_le_rate_mul_of_pos_norm hgap hstrict hnorm)

/-- An entrywise comparison is not needed once a finite reflection quadratic
already has an absolute rate bound.  If the rate is strictly below one and the
coefficient `l¹` mass is positive, the quadratic is strictly below its
coefficient square.  This is the direct consumer for physical finite-sector
absolute-form certificates; it does not manufacture the absolute bound or any
uniformity in its parameters. -/
theorem finiteJointQuadratic_lt_square_of_abs_rate
    {State : Type}
    (states : List State) (coefficient : State → Q')
    (comparedLaw : State → State → Q')
    (rate : Q')
    (hgap : Q'.abs (finiteJointQuadratic states coefficient comparedLaw) ≤
      rate * (coefficientL1 states coefficient * coefficientL1 states coefficient))
    (hstrict : rate < (1 : Q'))
    (hcoefficient : (0 : Q') < coefficientL1 states coefficient) :
    finiteJointQuadratic states coefficient comparedLaw <
      coefficientL1 states coefficient * coefficientL1 states coefficient := by
  let norm := coefficientL1 states coefficient * coefficientL1 states coefficient
  have hnorm : (0 : Q') < norm :=
    Q'.mul_pos hcoefficient hcoefficient
  exact lt_of_abs_le_rate_mul_of_pos_norm
    hgap
    hstrict hnorm

#print axioms abs_listQSum_sub_le
#print axioms listQSum_mono
#print axioms abs_common_mul_sub_le
#print axioms coefficientPairL1_le_square
#print axioms finiteJointQuadratic_abs_sub_le_pairL1
#print axioms finiteJointQuadratic_abs_sub_le_square
#print axioms ge_neg_of_reference_nonnegative
#print axioms finiteJointQuadratic_ge_neg_square_modulus
#print axioms le_reference_add_of_abs_sub_le
#print axioms upper_rate_of_reference_gap_and_abs_error
#print axioms finiteJointQuadratic_le_reference_rate_add_error
#print axioms finiteJointQuadratic_lt_square_of_reference_rate_and_abs_error
#print axioms abs_lt_of_abs_le_rate_mul_of_pos_norm
#print axioms lt_of_abs_le_rate_mul_of_pos_norm
#print axioms finiteJointQuadratic_lt_square_of_abs_rate

end YMGap.Continuum.Z4FiniteCylinderQuadraticStability
