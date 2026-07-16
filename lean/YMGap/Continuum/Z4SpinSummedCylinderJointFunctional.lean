/-
# The joint-cutoff thermodynamic cylinder probability functional

The simultaneous representation-cutoff/volume limits are assembled into a
normalized positive finitely additive functional on every finite Boolean
cylinder algebra.  Appending ignored coordinates leaves the functional
unchanged.  All identities are inherited pointwise from the exact finite gas;
no limiting compactness or choice principle is used.
-/

import YMGap.Constructive.CRealAdd
import YMGap.Continuum.Z4CanonicalCylinderFunctional
import YMGap.Continuum.Z4SpinSummedCylinderJointCofinal

namespace YMGap.Continuum.Z4SpinSummedCylinderJointFunctional

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalCylinderCofinal
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderFunctional
open YMGap.Continuum.Z4CanonicalCylinderStability
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedCutoffTail
open YMGap.Continuum.Z4SpinSummedCylinderJointCofinal
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact finite-gas Boolean identities at arbitrary cutoff -/

private theorem listQSum_filter_or_disjoint_local {A : Type}
    (weight : A → Q') (first second : A → Bool) :
    ∀ xs : List A,
      (∀ x, x ∈ xs → first x = true → second x = false) →
      listQSum weight
          (xs.filter (fun x => first x || second x)) ≈
        listQSum weight (xs.filter first) +
          listQSum weight (xs.filter second)
  | [], _ => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))
  | head :: tail, hdisjoint => by
      have htail := listQSum_filter_or_disjoint_local
        weight first second tail
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
          (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)) ?_
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

theorem parametricKCompatibleEventNumerator_union_eqv_add
    (cutoff n : Nat) (first second : List (List Nat) → Bool)
    (hdisjoint : ∀ family, first family = true →
      second family = false) :
    parametricKCompatibleSupportEventNumerator cutoff n
        (fun family => first family || second family) ≈
      parametricKCompatibleSupportEventNumerator cutoff n first +
        parametricKCompatibleSupportEventNumerator cutoff n second := by
  unfold parametricKCompatibleSupportEventNumerator
  exact listQSum_filter_or_disjoint_local
    (parametricKSupportFamilyActivity cutoff n) first second
    (canonicalCompatibleAmbientFamilies n)
    (fun family _ => hdisjoint family)

theorem parametricKCompatibleEventProbability_union_eqv_add
    (cutoff n : Nat) (first second : List (List Nat) → Bool)
    (hdisjoint : ∀ family, first family = true →
      second family = false) :
    parametricKCompatibleSupportEventProbability cutoff n
        (fun family => first family || second family) ≈
      parametricKCompatibleSupportEventProbability cutoff n first +
        parametricKCompatibleSupportEventProbability cutoff n second := by
  have hnumerator :=
    parametricKCompatibleEventNumerator_union_eqv_add
      cutoff n first second hdisjoint
  unfold parametricKCompatibleSupportEventProbability Q'.divPos
  refine Q'.eqv_trans _
    ((parametricKCompatibleSupportEventNumerator cutoff n first +
        parametricKCompatibleSupportEventNumerator cutoff n second) *
      Q'.recipPos (parametricKCompatibleSupportGasPartition cutoff n)
        (parametricKCompatibleSupportGasPartition_pos cutoff n)) _
    (Q'.mul_eqv_congr_right _ _ _ hnumerator) ?_
  exact Q'.add_mul_eqv
    (parametricKCompatibleSupportEventNumerator cutoff n first)
    (parametricKCompatibleSupportEventNumerator cutoff n second)
    (Q'.recipPos (parametricKCompatibleSupportGasPartition cutoff n)
      (parametricKCompatibleSupportGasPartition_pos cutoff n))

theorem parametricKCompatibleCylinderProbability_union_eqv_add
    (cutoff base n : Nat) (roots : List (List Nat))
    (first second : List Bool → Bool)
    (hdisjoint : CylinderPredicatesDisjoint first second) :
    parametricKCompatibleSupportEventProbability cutoff n
        (targetCylinderEvent base n roots
          (cylinderPredicateUnion first second)) ≈
      parametricKCompatibleSupportEventProbability cutoff n
          (targetCylinderEvent base n roots first) +
        parametricKCompatibleSupportEventProbability cutoff n
          (targetCylinderEvent base n roots second) := by
  apply parametricKCompatibleEventProbability_union_eqv_add
  intro family hfirst
  exact hdisjoint
    (familyOccurrenceFingerprint
      (transportedCylinderRoots base n roots) family) hfirst

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

theorem parametricKCompatibleEventProbability_true_eqv_one
    (cutoff n : Nat) :
    parametricKCompatibleSupportEventProbability cutoff n
        (fun _ => true) ≈ (1 : Q') := by
  have hnumerator :
      parametricKCompatibleSupportEventNumerator cutoff n
          (fun _ => true) ≈
        parametricKCompatibleSupportGasPartition cutoff n := by
    unfold parametricKCompatibleSupportEventNumerator
      parametricKCompatibleSupportGasPartition
    rw [filter_true_local]
    exact Q'.eqv_refl _
  unfold parametricKCompatibleSupportEventProbability Q'.divPos
  refine Q'.eqv_trans _
    (parametricKCompatibleSupportGasPartition cutoff n *
      Q'.recipPos (parametricKCompatibleSupportGasPartition cutoff n)
        (parametricKCompatibleSupportGasPartition_pos cutoff n)) _
    (Q'.mul_eqv_congr_right _ _ _ hnumerator) ?_
  exact Q'.mul_recipPos_eqv
    (parametricKCompatibleSupportGasPartition cutoff n)
    (parametricKCompatibleSupportGasPartition_pos cutoff n)

theorem parametricKCompatibleEventProbability_false_eqv_zero
    (cutoff n : Nat) :
    parametricKCompatibleSupportEventProbability cutoff n
        (fun _ => false) ≈ (0 : Q') := by
  have hnumerator :
      parametricKCompatibleSupportEventNumerator cutoff n
          (fun _ => false) ≈ (0 : Q') := by
    unfold parametricKCompatibleSupportEventNumerator
    rw [filter_false_local]
    exact Q'.eqv_refl _
  unfold parametricKCompatibleSupportEventProbability Q'.divPos
  refine Q'.eqv_trans _
    ((0 : Q') *
      Q'.recipPos (parametricKCompatibleSupportGasPartition cutoff n)
        (parametricKCompatibleSupportGasPartition_pos cutoff n)) _
    (Q'.mul_eqv_congr_right _ _ _ hnumerator) ?_
  exact Q'.zero_mul_eqv _

/-! ## 2. The normalized positive joint-limit functional -/

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

private theorem two_sided_add_of_abs_sub_le_local
    {a b epsilon : Q'}
    (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

def spinSummedJointCylinderLimitFunctional
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (List Bool → Bool) → CReal :=
  spinSummedJointCylinderLimit hroots

theorem spinSummedJointCylinderLimitFunctional_nonnegative
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.ofQ' 0 ≤
      spinSummedJointCylinderLimitFunctional hroots predicate :=
  spinSummedJointCylinderLimit_nonnegative hroots predicate

theorem spinSummedJointCylinderLimitFunctional_le_one
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    spinSummedJointCylinderLimitFunctional hroots predicate ≤
      CReal.ofQ' 1 :=
  spinSummedJointCylinderLimit_le_one hroots predicate

theorem spinSummedJointCylinderLimitFunctional_normalized
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    CReal.Equiv
      (spinSummedJointCylinderLimitFunctional hroots (fun _ => true))
      (CReal.ofQ' 1) := by
  apply creal_equiv_of_approx_eqv_local
  intro stage
  exact parametricKCompatibleEventProbability_true_eqv_one
    (spinSummedJointCutoff stage (base + stage)) (base + stage)

theorem spinSummedJointCylinderLimitFunctional_empty
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    CReal.Equiv
      (spinSummedJointCylinderLimitFunctional hroots (fun _ => false))
      (CReal.ofQ' 0) := by
  apply creal_equiv_of_approx_eqv_local
  intro stage
  exact parametricKCompatibleEventProbability_false_eqv_zero
    (spinSummedJointCutoff stage (base + stage)) (base + stage)

theorem spinSummedJointCylinderLimitFunctional_complement
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.Equiv
      (CReal.add
        (spinSummedJointCylinderLimitFunctional hroots predicate)
        (spinSummedJointCylinderLimitFunctional hroots
          (complementCylinderPredicate predicate)))
      (CReal.ofQ' 1) := by
  apply creal_equiv_of_approx_eqv_local
  intro stage
  exact parametricKCompatibleEventProbability_add_complement_eqv_one
    (spinSummedJointCutoff stage (base + stage)) (base + stage)
    (targetCylinderEvent base (base + stage) roots predicate)

theorem spinSummedJointCylinderLimitFunctional_disjoint_additive
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (first second : List Bool → Bool)
    (hdisjoint : CylinderPredicatesDisjoint first second) :
    CReal.Equiv
      (spinSummedJointCylinderLimitFunctional hroots
        (cylinderPredicateUnion first second))
      (CReal.add
        (spinSummedJointCylinderLimitFunctional hroots first)
        (spinSummedJointCylinderLimitFunctional hroots second)) := by
  apply creal_equiv_of_approx_eqv_local
  intro stage
  exact parametricKCompatibleCylinderProbability_union_eqv_add
    (spinSummedJointCutoff stage (base + stage))
    base (base + stage) roots first second hdisjoint

/-! ## 3. Projective consistency under ignored-coordinate refinement -/

theorem spinSummedJointCylinderLimitFunctional_refinement
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
      (spinSummedJointCylinderLimitFunctional happend
        (extendCylinderPredicate roots.length predicate))
      (spinSummedJointCylinderLimitFunctional hroots predicate) := by
  intro happend
  apply creal_equiv_of_approx_eqv_local
  intro stage
  change parametricKCompatibleSupportEventProbability
      (spinSummedJointCutoff stage (base + stage)) (base + stage)
      (targetCylinderEvent base (base + stage) (roots ++ extra)
        (extendCylinderPredicate roots.length predicate)) ≈
    parametricKCompatibleSupportEventProbability
      (spinSummedJointCutoff stage (base + stage)) (base + stage)
      (targetCylinderEvent base (base + stage) roots predicate)
  rw [targetCylinderEvent_append_extend]
  exact Q'.eqv_refl _

/-! ## 4. Independence of the finite box presenting a local cylinder -/

theorem spinSummedJointCylinderLimitFunctional_base_transport
    {base outerBase : Nat} (hbase : base ≤ outerBase)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    let htransported : ∀ root,
        root ∈ transportedCylinderRoots base outerBase roots →
          root ∈ canonicalSurfacePolymers outerBase :=
      transportedCylinderRoots_canonical hbase hroots
    CReal.Equiv
      (spinSummedJointCylinderLimitFunctional htransported predicate)
      (spinSummedJointCylinderLimitFunctional hroots predicate) := by
  intro htransported
  intro epsilon hepsilon
  let coefficient := spinSummedJointCylinderCoefficient roots.length
  let scaledTolerance :=
    epsilon * Q'.invSucc coefficient.num.toNat
  have hcoefficient : (0 : Q') ≤ coefficient :=
    spinSummedJointCylinderCoefficient_nonnegative roots.length
  have hscaledPositive : (0 : Q') < scaledTolerance :=
    Q'.mul_pos hepsilon (Q'.invSucc_pos coefficient.num.toNat)
  have hscaledFinal : coefficient * scaledTolerance ≤ epsilon :=
    ExpNeg.mul_le_of_mul_invSucc_toNat coefficient epsilon
      hcoefficient (Q'.le_of_lt hepsilon)
  refine ⟨scaledTolerance.den, fun stage hstage => ?_⟩
  have hraw :=
    spinSummedJointCylinderSequence_base_transport_abs_le
      hbase hroots predicate (stage := stage)
  obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hstage
  have hhalf : HalfPow.half ^ stage ≤
      HalfPow.half ^ scaledTolerance.den := by
    rw [hoffset]
    exact ExpNeg.pow_half_antitone scaledTolerance.den offset
  have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
      scaledTolerance :=
    HalfPow.pow_half_le scaledTolerance hscaledPositive
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (HalfPow.half ^ stage) scaledTolerance coefficient
    (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
  have habs :
      Q'.abs
          (spinSummedJointCylinderSequence outerBase
              (transportedCylinderRoots base outerBase roots)
              predicate stage -
            spinSummedJointCylinderSequence base roots predicate stage) ≤
        epsilon :=
    Q'.le_trans' _ _ _ hraw
      (Q'.le_trans' _ _ _ hscaled hscaledFinal)
  exact two_sided_add_of_abs_sub_le_local habs

#print axioms parametricKCompatibleCylinderProbability_union_eqv_add
#print axioms parametricKCompatibleEventProbability_true_eqv_one
#print axioms spinSummedJointCylinderLimitFunctional_normalized
#print axioms spinSummedJointCylinderLimitFunctional_complement
#print axioms spinSummedJointCylinderLimitFunctional_disjoint_additive
#print axioms spinSummedJointCylinderLimitFunctional_refinement
#print axioms spinSummedJointCylinderLimitFunctional_base_transport

end YMGap.Continuum.Z4SpinSummedCylinderJointFunctional
