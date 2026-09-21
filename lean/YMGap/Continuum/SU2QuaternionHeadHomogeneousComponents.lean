/-
# Exact head-homogeneous components of a rational quaternion polynomial

Every finite rational polynomial splits constructively into the filters of
its exact degree in quaternion block zero.  The explicit degree-sum bound
contains every term, and the finite component sum is coefficient-equivalent
to the original polynomial.  This is only a homogeneous decomposition: no
component is asserted harmonic.
-/

import YMGap.Continuum.SU2QuaternionHeadDegreeDifferential

namespace YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadDegreeDifferential

/-- The terms having exactly `degree` in quaternion block zero. -/
def headComponent (degree : Nat) (p : RatPoly) : RatPoly :=
  p.filter fun term => decide (quaternionBlockDegree term.1 0 = degree)

/-- A computable inclusive upper bound for every head degree in `p`. -/
def headDegreeBound (p : RatPoly) : Nat := quaternionBlockDegreeSum 0 p

/-- The finite list of all possible head degrees of `p`. -/
def headDegrees (p : RatPoly) : List Nat := List.range (headDegreeBound p + 1)

/-- The explicit finite sum of all exact head-degree filters. -/
def headComponentSum (p : RatPoly) : RatPoly :=
  polySum ((headDegrees p).map fun degree => headComponent degree p)

theorem headComponent_degree (degree : Nat) (p : RatPoly) :
    HasQuaternionBlockDegree 0 degree (headComponent degree p) := by
  intro term hterm
  exact of_decide_eq_true (List.mem_filter.mp hterm).2

theorem headComponent_supported {blocks degree : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (headComponent degree p) := by
  intro term hterm
  exact hp term (List.mem_filter.mp hterm).1

/-- Filtering preserves every per-term predicate, including head padding. -/
theorem headComponent_termwise {degree : Nat} {p : RatPoly}
    (predicate : RatTerm -> Prop)
    (hp : forall term, term ∈ p -> predicate term) :
    forall term, term ∈ headComponent degree p -> predicate term := by
  intro term hterm
  exact hp term (List.mem_filter.mp hterm).1

/-- In particular, a minimum exponent-list length is inherited by a component. -/
theorem headComponent_min_length {minimum degree : Nat} {p : RatPoly}
    (hp : forall term, term ∈ p -> minimum ≤ term.1.length) :
    forall term, term ∈ headComponent degree p -> minimum ≤ term.1.length :=
  headComponent_termwise (fun term => minimum ≤ term.1.length) hp

theorem headDegree_le_bound {term : RatTerm} : forall {p : RatPoly},
    term ∈ p -> quaternionBlockDegree term.1 0 ≤ headDegreeBound p
  | [], hterm => by cases hterm
  | head :: rest, hterm => by
      rcases List.mem_cons.mp hterm with rfl | hterm
      · simp [headDegreeBound, quaternionBlockDegreeSum]
      · have ih := headDegree_le_bound hterm
        unfold headDegreeBound at ih ⊢
        simp only [quaternionBlockDegreeSum]
        omega

theorem headComponent_mem_iff {degree : Nat} {p : RatPoly} {term : RatTerm} :
    term ∈ headComponent degree p ↔
      term ∈ p ∧ quaternionBlockDegree term.1 0 = degree := by
  simp only [headComponent, List.mem_filter, decide_eq_true_eq]

private theorem polySum_append_exact : forall first second : List RatPoly,
    polySum (first ++ second) = polyAdd (polySum first) (polySum second)
  | [], _ => rfl
  | polynomial :: rest, second => by
      simp only [List.cons_append, polySum, polySum_append_exact rest second,
        polyAdd, List.append_assoc]

private theorem polySum_congr {A : Type} (f g : A -> RatPoly) :
    forall xs : List A,
      (forall x, x ∈ xs -> RatPolyCoeffEqv (f x) (g x)) ->
      RatPolyCoeffEqv (polySum (xs.map f)) (polySum (xs.map g))
  | [], _ => RatPolyCoeffEqv.refl _
  | x :: xs, h =>
      (h x List.mem_cons_self).add
        (polySum_congr f g xs (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem polySum_pointwise_add {A : Type} (f g : A -> RatPoly) :
    forall xs : List A,
      RatPolyCoeffEqv
        (polySum (xs.map fun x => polyAdd (f x) (g x)))
        (polyAdd (polySum (xs.map f)) (polySum (xs.map g)))
  | [] => RatPolyCoeffEqv.refl _
  | x :: xs => by
      change RatPolyCoeffEqv
        (polyAdd (polyAdd (f x) (g x))
          (polySum (xs.map fun y => polyAdd (f y) (g y))))
        (polyAdd (polyAdd (f x) (polySum (xs.map f)))
          (polyAdd (g x) (polySum (xs.map g))))
      exact ((RatPolyCoeffEqv.refl _).add (polySum_pointwise_add f g xs)).trans
        (RatPolyCoeffEqv.four_add_swap (f x) (g x)
          (polySum (xs.map f)) (polySum (xs.map g)))

private theorem absent_singleton_sum (term : RatTerm) (degree : Nat) :
    forall xs : List Nat,
      (forall n, n ∈ xs -> degree ≠ n) ->
      polySum (xs.map fun n => if degree = n then [term] else polyZero) = polyZero
  | [], _ => rfl
  | n :: xs, h => by
      have hn : degree ≠ n := h n List.mem_cons_self
      have hrest : forall k, k ∈ xs -> degree ≠ k :=
        fun k hk => h k (List.mem_cons_of_mem n hk)
      simp only [List.map_cons, if_neg hn, polySum,
        absent_singleton_sum term degree xs hrest]
      rfl

private theorem singleton_sum_range (term : RatTerm) : forall bound degree : Nat,
    degree < bound ->
    polySum ((List.range bound).map fun n =>
      if degree = n then [term] else polyZero) = [term]
  | 0, _, h => by omega
  | bound + 1, degree, h => by
      rw [List.range_succ, List.map_append, polySum_append_exact]
      by_cases hlt : degree < bound
      · have hne : degree ≠ bound := Nat.ne_of_lt hlt
        rw [singleton_sum_range term bound degree hlt]
        simp [hne, polySum, polyAdd, polyZero]
      · have heq : degree = bound := by omega
        subst degree
        have habsent : forall n, n ∈ List.range bound -> bound ≠ n := by
          intro n hn heq'
          subst n
          exact (Nat.lt_irrefl bound) (List.mem_range.mp hn)
        rw [absent_singleton_sum term bound (List.range bound) habsent]
        simp [polySum, polyAdd, polyZero]

private theorem headComponent_cons (degree : Nat) (term : RatTerm) (p : RatPoly) :
    headComponent degree (term :: p) =
      polyAdd
        (if quaternionBlockDegree term.1 0 = degree then [term] else polyZero)
        (headComponent degree p) := by
  unfold headComponent
  by_cases hdegree : quaternionBlockDegree term.1 0 = degree
  · simp [hdegree, polyAdd]
  · simp [hdegree, polyAdd, polyZero]

private theorem reassembly_up_to : forall (p : RatPoly) (bound : Nat),
    (forall term, term ∈ p -> quaternionBlockDegree term.1 0 < bound) ->
    RatPolyCoeffEqv
      (polySum ((List.range bound).map fun degree => headComponent degree p)) p
  | [], _, _ => by
      have hnil : ∀ xs : List Nat,
          polySum (xs.map fun degree => headComponent degree []) = [] := by
        intro xs
        induction xs with
        | nil => rfl
        | cons x xs ih => simpa [polySum, headComponent, polyAdd] using ih
      rw [hnil]
      exact RatPolyCoeffEqv.refl _
  | term :: rest, bound, hbound => by
      let singletonPart : Nat -> RatPoly := fun degree =>
        if quaternionBlockDegree term.1 0 = degree then [term] else polyZero
      let restPart : Nat -> RatPoly := fun degree => headComponent degree rest
      have hcomponents : forall degree, degree ∈ List.range bound ->
          RatPolyCoeffEqv (headComponent degree (term :: rest))
            (polyAdd (singletonPart degree) (restPart degree)) := by
        intro degree _
        dsimp only [singletonPart, restPart]
        rw [headComponent_cons]
        exact RatPolyCoeffEqv.refl _
      have hterm : quaternionBlockDegree term.1 0 < bound :=
        hbound term List.mem_cons_self
      have hrest : forall t, t ∈ rest -> quaternionBlockDegree t.1 0 < bound :=
        fun t ht => hbound t (List.mem_cons_of_mem term ht)
      refine (polySum_congr _ _ (List.range bound) hcomponents).trans ?_
      refine (polySum_pointwise_add singletonPart restPart (List.range bound)).trans ?_
      have hsingle :
          polySum ((List.range bound).map singletonPart) = [term] :=
        singleton_sum_range term bound (quaternionBlockDegree term.1 0) hterm
      rw [hsingle]
      exact (RatPolyCoeffEqv.refl [term]).add (reassembly_up_to rest bound hrest)

/-- Coefficient-exact reassembly of all head-homogeneous components. -/
theorem headComponent_reassembly (p : RatPoly) :
    RatPolyCoeffEqv (headComponentSum p) p := by
  unfold headComponentSum headDegrees
  apply reassembly_up_to
  intro term hterm
  have hle := headDegree_le_bound hterm
  omega

/-- Every enumerated component is syntactically homogeneous at its label. -/
theorem headComponents_degree (p : RatPoly) {degree : Nat}
    (_hdegree : degree ∈ headDegrees p) :
    HasQuaternionBlockDegree 0 degree (headComponent degree p) :=
  headComponent_degree degree p

/-- Support is inherited uniformly by every enumerated component. -/
theorem headComponents_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) {degree : Nat}
    (_hdegree : degree ∈ headDegrees p) :
    SupportedQuaternionBlocks blocks (headComponent degree p) :=
  headComponent_supported hp

end YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents

#print axioms YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents.headComponent_degree
#print axioms YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents.headComponent_supported
#print axioms YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents.headComponent_termwise
#print axioms YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents.headComponent_min_length
#print axioms YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents.headDegree_le_bound
#print axioms YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents.headComponent_mem_iff
#print axioms YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents.headComponent_reassembly
#print axioms YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents.headComponents_degree
#print axioms YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents.headComponents_supported
