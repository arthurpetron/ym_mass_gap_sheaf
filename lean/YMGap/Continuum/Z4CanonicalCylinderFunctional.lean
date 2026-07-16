/-
# The positive consistent finite-cylinder limit functional

The constructive-real cylinder limits are assembled into a normalized
positive finitely additive functional on Boolean predicates of a finite
occurrence fingerprint.  Extending a cylinder by extra marked polymers while
ignoring the new coordinates leaves the limit unchanged, giving the basic
projective consistency relation.
-/

import YMGap.Constructive.CRealAdd
import YMGap.Continuum.Z4CanonicalCylinderCofinal

namespace YMGap.Continuum.Z4CanonicalCylinderFunctional

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalCylinderCofinal
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderStability
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite-volume Boolean additivity -/

def cylinderPredicateUnion
    (first second : List Bool → Bool) : List Bool → Bool :=
  fun bits => first bits || second bits

def CylinderPredicatesDisjoint
    (first second : List Bool → Bool) : Prop :=
  ∀ bits, first bits = true → second bits = false

private theorem listQSum_filter_or_disjoint {A : Type}
    (weight : A → Q') (first second : A → Bool) :
    ∀ xs : List A,
      (∀ x, x ∈ xs → first x = true → second x = false) →
      listQSum weight
          (xs.filter (fun x => first x || second x)) ≈
        listQSum weight (xs.filter first) +
          listQSum weight (xs.filter second)
  | [], _ =>
      Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))
  | head :: tail, hdisjoint => by
      have htail := listQSum_filter_or_disjoint weight first second tail
        (fun x hx => hdisjoint x (List.mem_cons_of_mem head hx))
      cases hfirst : first head <;> cases hsecond : second head
      · simpa [hfirst, hsecond] using htail
      · simp only [List.filter_cons, hfirst, hsecond, Bool.false_or,
          ↓reduceIte, listQSum]
        refine Q'.eqv_trans _
          (weight head +
            (listQSum weight (tail.filter first) +
              listQSum weight (tail.filter second))) _
          (Q'.add_eqv_congr_left (weight head) _ _ htail) ?_
        refine Q'.eqv_trans _
          ((weight head + listQSum weight (tail.filter first)) +
            listQSum weight (tail.filter second)) _
          (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
        refine Q'.eqv_trans _
          ((listQSum weight (tail.filter first) + weight head) +
            listQSum weight (tail.filter second)) _
          (Q'.add_eqv_congr_right _ _ _
            (Q'.add_comm_eqv _ _)) ?_
        exact Q'.add_assoc_eqv _ _ _
      · simp only [List.filter_cons, hfirst, hsecond, Bool.true_or,
          ↓reduceIte, listQSum]
        refine Q'.eqv_trans _
          (weight head +
            (listQSum weight (tail.filter first) +
              listQSum weight (tail.filter second))) _
          (Q'.add_eqv_congr_left (weight head) _ _ htail) ?_
        exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
      · have hfalse := hdisjoint head List.mem_cons_self hfirst
        simp_all

theorem anchorEventNumerator_union_eqv_add
    (n : Nat) (first second : List (List Nat) → Bool)
    (hdisjoint : ∀ family, first family = true → second family = false) :
    anchorEventNumerator n (fun family => first family || second family) ≈
      anchorEventNumerator n first + anchorEventNumerator n second := by
  unfold anchorEventNumerator
  exact listQSum_filter_or_disjoint
    (canonicalSurfaceFamilyActivity anchorCoupling n) first second
    (canonicalCompatibleAmbientFamilies n)
    (fun family _ => hdisjoint family)

theorem anchorEventProbability_union_eqv_add
    (n : Nat) (first second : List (List Nat) → Bool)
    (hdisjoint : ∀ family, first family = true → second family = false) :
    anchorEventProbability n (fun family => first family || second family) ≈
      anchorEventProbability n first + anchorEventProbability n second := by
  have hnumerator := anchorEventNumerator_union_eqv_add
    n first second hdisjoint
  unfold anchorEventProbability Q'.divPos
  refine Q'.eqv_trans _
    ((anchorEventNumerator n first + anchorEventNumerator n second) *
      Q'.recipPos (anchorCanonicalPartition n)
        (anchorCanonicalPartition_pos n)) _
    (Q'.mul_eqv_congr_right _ _ _ hnumerator) ?_
  exact Q'.add_mul_eqv
    (anchorEventNumerator n first)
    (anchorEventNumerator n second)
    (Q'.recipPos (anchorCanonicalPartition n)
      (anchorCanonicalPartition_pos n))

theorem anchorCylinderProbability_union_eqv_add
    (n : Nat) (roots : List (List Nat))
    (first second : List Bool → Bool)
    (hdisjoint : CylinderPredicatesDisjoint first second) :
    anchorEventProbability n
        (cylinderEvent roots (cylinderPredicateUnion first second)) ≈
      anchorEventProbability n (cylinderEvent roots first) +
        anchorEventProbability n (cylinderEvent roots second) := by
  apply anchorEventProbability_union_eqv_add
  intro family hfirst
  exact hdisjoint (familyOccurrenceFingerprint roots family) hfirst

private theorem filter_true_local {A : Type} :
    ∀ xs : List A, xs.filter (fun _ => true) = xs
  | [] => rfl
  | head :: tail => by
      change head :: tail.filter (fun _ => true) = head :: tail
      exact congrArg (List.cons head) (filter_true_local tail)

private theorem filter_false_local {A : Type} :
    ∀ xs : List A, xs.filter (fun _ => false) = []
  | [] => rfl
  | _ :: tail => filter_false_local tail

theorem anchorEventProbability_true_eqv_one (n : Nat) :
    anchorEventProbability n (fun _ => true) ≈ (1 : Q') := by
  have hnumerator :
      anchorEventNumerator n (fun _ => true) ≈
        anchorCanonicalPartition n := by
    unfold anchorEventNumerator anchorCanonicalPartition
      parametricCanonicalCompatibleAmbientPartition
    rw [filter_true_local]
    exact Q'.eqv_refl _
  unfold anchorEventProbability Q'.divPos
  refine Q'.eqv_trans _
    (anchorCanonicalPartition n *
      Q'.recipPos (anchorCanonicalPartition n)
        (anchorCanonicalPartition_pos n)) _
    (Q'.mul_eqv_congr_right _ _ _ hnumerator) ?_
  exact Q'.mul_recipPos_eqv
    (anchorCanonicalPartition n) (anchorCanonicalPartition_pos n)

theorem anchorEventProbability_false_eqv_zero (n : Nat) :
    anchorEventProbability n (fun _ => false) ≈ (0 : Q') := by
  have hnumerator :
      anchorEventNumerator n (fun _ => false) ≈ (0 : Q') := by
    unfold anchorEventNumerator
    rw [filter_false_local]
    exact Q'.eqv_refl _
  unfold anchorEventProbability Q'.divPos
  refine Q'.eqv_trans _
    ((0 : Q') * Q'.recipPos (anchorCanonicalPartition n)
      (anchorCanonicalPartition_pos n)) _
    (Q'.mul_eqv_congr_right _ _ _ hnumerator) ?_
  exact Q'.zero_mul_eqv _

/-! ## 2. Lifting exact finite identities to constructive-real limits -/

private theorem equiv_ofQ'_of_eqv_local {a b : Q'} (h : a ≈ b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) := by
  intro epsilon hepsilon
  refine ⟨0, fun _ _ => ?_⟩
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h)
      (Q'.add_le_self_of_nonneg b epsilon (Q'.le_of_lt hepsilon))
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv h)
      (Q'.add_le_self_of_nonneg a epsilon (Q'.le_of_lt hepsilon))

private theorem creal_equiv_of_approx_eqv_local {A B : CReal}
    (h : ∀ stage, A.approx stage ≈ B.approx stage) :
    CReal.Equiv A B :=
  CReal.Equiv_of_lifted_approx_equal
    (fun stage => equiv_ofQ'_of_eqv_local (h stage))

def anchorCylinderLimitFunctional
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (List Bool → Bool) → CReal :=
  anchorCylinderCofinalLimit hroots

theorem anchorCylinderLimitFunctional_nonnegative
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.ofQ' 0 ≤ anchorCylinderLimitFunctional hroots predicate :=
  anchorCylinderCofinalLimit_nonnegative hroots predicate

theorem anchorCylinderLimitFunctional_normalized
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    CReal.Equiv
      (anchorCylinderLimitFunctional hroots (fun _ => true))
      (CReal.ofQ' 1) := by
  apply creal_equiv_of_approx_eqv_local
  intro stage
  exact anchorEventProbability_true_eqv_one (base + stage)

theorem anchorCylinderLimitFunctional_empty
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    CReal.Equiv
      (anchorCylinderLimitFunctional hroots (fun _ => false))
      (CReal.ofQ' 0) := by
  apply creal_equiv_of_approx_eqv_local
  intro stage
  exact anchorEventProbability_false_eqv_zero (base + stage)

theorem anchorCylinderLimitFunctional_complement
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.Equiv
      (CReal.add
        (anchorCylinderLimitFunctional hroots predicate)
        (anchorCylinderLimitFunctional hroots
          (complementCylinderPredicate predicate)))
      (CReal.ofQ' 1) := by
  apply creal_equiv_of_approx_eqv_local
  intro stage
  exact anchorEventProbability_add_complement_eqv_one
    (base + stage)
    (targetCylinderEvent base (base + stage) roots predicate)

theorem anchorCylinderLimitFunctional_disjoint_additive
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (first second : List Bool → Bool)
    (hdisjoint : CylinderPredicatesDisjoint first second) :
    CReal.Equiv
      (anchorCylinderLimitFunctional hroots
        (cylinderPredicateUnion first second))
      (CReal.add
        (anchorCylinderLimitFunctional hroots first)
        (anchorCylinderLimitFunctional hroots second)) := by
  apply creal_equiv_of_approx_eqv_local
  intro stage
  exact anchorCylinderProbability_union_eqv_add
    (base + stage)
    (transportedCylinderRoots base (base + stage) roots)
    first second hdisjoint

/-! ## 3. Projective consistency under cylinder refinement -/

def extendCylinderPredicate (prefixLength : Nat)
    (predicate : List Bool → Bool) : List Bool → Bool :=
  fun bits => predicate (bits.take prefixLength)

theorem cylinderEvent_append_extend
    (roots extra : List (List Nat)) (predicate : List Bool → Bool) :
    cylinderEvent (roots ++ extra)
        (extendCylinderPredicate roots.length predicate) =
      cylinderEvent roots predicate := by
  funext family
  unfold cylinderEvent extendCylinderPredicate familyOccurrenceFingerprint
  rw [List.map_append, List.take_append]
  have hlength : roots.length =
      (List.map (fun root => familyContainsPolymerB root family) roots).length := by
    simp only [List.length_map]
  rw [hlength, List.take_length]
  simp only [List.length_map, Nat.sub_self, List.take_zero, List.append_nil]

theorem targetCylinderEvent_append_extend
    (base outer : Nat) (roots extra : List (List Nat))
    (predicate : List Bool → Bool) :
    targetCylinderEvent base outer (roots ++ extra)
        (extendCylinderPredicate roots.length predicate) =
      targetCylinderEvent base outer roots predicate := by
  unfold targetCylinderEvent transportedCylinderRoots
  rw [List.map_append]
  have hlength :
      (List.map (transportPolymer base outer) roots).length = roots.length := by
    simp only [List.length_map]
  rw [← hlength]
  exact cylinderEvent_append_extend
    (List.map (transportPolymer base outer) roots)
    (List.map (transportPolymer base outer) extra) predicate

theorem anchorCylinderLimitFunctional_refinement
    {base : Nat} {roots extra : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (hextra : ∀ root, root ∈ extra →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    let happend : ∀ root, root ∈ roots ++ extra →
        root ∈ canonicalSurfacePolymers base :=
      fun root hroot => by
        rcases List.mem_append.mp hroot with hleft | hright
        · exact hroots root hleft
        · exact hextra root hright
    CReal.Equiv
      (anchorCylinderLimitFunctional happend
        (extendCylinderPredicate roots.length predicate))
      (anchorCylinderLimitFunctional hroots predicate) := by
  intro happend
  apply creal_equiv_of_approx_eqv_local
  intro stage
  change anchorEventProbability (base + stage)
      (targetCylinderEvent base (base + stage) (roots ++ extra)
        (extendCylinderPredicate roots.length predicate)) ≈
    anchorEventProbability (base + stage)
      (targetCylinderEvent base (base + stage) roots predicate)
  rw [targetCylinderEvent_append_extend]
  exact Q'.eqv_refl _

end YMGap.Continuum.Z4CanonicalCylinderFunctional

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalCylinderFunctional.anchorCylinderLimitFunctional_nonnegative
#print axioms YMGap.Continuum.Z4CanonicalCylinderFunctional.anchorCylinderLimitFunctional_normalized
#print axioms YMGap.Continuum.Z4CanonicalCylinderFunctional.anchorCylinderLimitFunctional_complement
#print axioms YMGap.Continuum.Z4CanonicalCylinderFunctional.anchorCylinderLimitFunctional_disjoint_additive
#print axioms YMGap.Continuum.Z4CanonicalCylinderFunctional.anchorCylinderLimitFunctional_refinement
