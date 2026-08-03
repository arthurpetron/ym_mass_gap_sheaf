/-
# Exact BF4 slab to the physical Perron carrier

The literal corrected-slab kernel is the signed 116-link Haar network.  Its
canonical vacuum normalization is already exact.  The Perron machinery, on
the other hand, is naturally phrased on the positive-row carrier of the
partition-normalized reflected physical joint law.

This file performs the algebraic part of the dependency reroute.

* The normalized full physical reflection quadratic is proved equal to the
  same quadratic after filtering precisely the zero-marginal rows.  Thus the
  full OS presentation and the reversible Perron presentation are the same
  finite quadratic form.
* `ExactHaarPhysicalPerronSameActionAt` is a certificate-independent named
  input identifying the literal exact Haar-network quadratic with that
  physical quadratic.  It does not depend on a grouped-Mehler spectral
  certificate.
* A symmetric-reference Perron comparison with total rate at most `1/4`
  transfers directly to the literal exact slab on the physical mean-zero
  carrier.  This bypasses the obstructed Haar-centered truncated-Gram route.
* More strongly, exact all-word gluing plus a genuine local `qS <= 1/4`
  contraction transfers the physical centered-row `1/16` directly to the
  exact quadratic.  This route uses no macro-slab spectral eighth, row-error
  eighth, or carrier-growth payment.

Honest scope: the same-action structure is deliberately not inhabited here.
The current positive reflected physical law is the multiplicity-product law;
identifying it with the signed exact Haar-network sum is precisely the open
fusion/holonomy resummation theorem.  The theorem below consumes that named
input but does not assume it silently.

## Axiom gate

Finite lists and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
import YMGap.Continuum.BF4LocalContractionGluing
import YMGap.Continuum.BF4SymmetricReferenceOperatorComparison

namespace YMGap.Continuum.BF4ExactPhysicalPerronReroute

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4LocalContractionGluing
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SymmetricReferenceOperatorComparison
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_filter_eq_of_zero_local
    {A : Type} (value : A → Q') (predicate : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items →
        predicate item = false →
        value item ≈ 0) →
      listQSum value (items.filter predicate) ≈
        listQSum value items
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      cases hp : predicate head with
      | false =>
          simp only [List.filter_cons, hp, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _ _ _
            (listQSum_filter_eq_of_zero_local
              value predicate tail
              (fun item hitem =>
                hzero item
                  (List.mem_cons_of_mem head hitem)))
            (Q'.eqv_symm
              (Q'.eqv_trans _ _ _
                (Q'.add_eqv_congr'
                  (hzero head List.mem_cons_self hp)
                  (Q'.eqv_refl _))
                (Q'.eqv_of_eq
                  (Q'.zero_add' _))))
      | true =>
          simp only [List.filter_cons, hp, if_true, listQSum]
          exact Q'.add_eqv_congr'
            (Q'.eqv_refl _)
            (listQSum_filter_eq_of_zero_local
              value predicate tail
              (fun item hitem =>
                hzero item
                  (List.mem_cons_of_mem head hitem)))

private theorem listQSum_eqv_zero_of_all_local
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≈ 0) →
      listQSum value items ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (hzero head List.mem_cons_self)
          (listQSum_eqv_zero_of_all_local value tail
            (fun item hitem =>
              hzero item
                (List.mem_cons_of_mem head hitem))))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

/-! ## 1. Full physical OS quadratic equals the Perron joint quadratic -/

/-- Filtering exactly the zero-marginal sources and targets does not alter
the normalized physical reflection quadratic.  This is the exact bridge
from the full OS presentation to the reversible positive-row Perron carrier.
-/
theorem centralPhysicalJointQuadratic_eq_normalizedFull
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (observable : EdgeLabelling → Q') :
    centralPhysicalJointQuadratic
        w hw K half observable ≈
      centralNormalizedFullPhysicalReflectionQuadratic
        w hw K half observable := by
  let states := centralHalfStates K half
  let positivePredicate : EdgeLabelling → Bool :=
    fun state =>
      decide ((0 : Q') <
        centralPhysicalRowMarginal w hw K half state)
  let term : EdgeLabelling → EdgeLabelling → Q' :=
    fun left right =>
      (observable left * observable right) *
        centralNormalizedPhysicalReflectedKernel
          w hw K half left right
  let rawTerm : EdgeLabelling → EdgeLabelling → Q' :=
    fun left right =>
      (observable left * observable right) *
        centralPhysicalReflectedKernel w K half left right
  let reciprocal :=
    Q'.recipPos
      (slabParametricKPhysicalPartition
        w K (centralExtent half))
      (slabParametricKPhysicalPartition_pos
        hw K (centralExtent half))
  have hinner :
      ∀ left,
        left ∈ states →
          listQSum (term left)
              (states.filter positivePredicate) ≈
            listQSum (term left) states := by
    intro left hleft
    apply listQSum_filter_eq_of_zero_local
    intro right hright hfalse
    have hnot :
        ¬ (0 : Q') <
          centralPhysicalRowMarginal
            w hw K half right := by
      simpa only [positivePredicate,
        decide_eq_false_iff_not] using hfalse
    have hentry :
        centralNormalizedPhysicalReflectedKernel
            w hw K half left right ≈ 0 :=
      centralNormalizedPhysicalReflectedKernel_eqv_zero_of_target_not_pos
        hleft hright hnot
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left
        (observable left * observable right) _ _ hentry)
      (Q'.mul_zero_eqv _)
  have hfiltered :
      listQSum
          (fun left =>
            listQSum (term left)
              (states.filter positivePredicate))
          (states.filter positivePredicate) ≈
        listQSum
          (fun left => listQSum (term left) states)
          states := by
    refine Q'.eqv_trans _
      (listQSum
        (fun left => listQSum (term left) states)
        (states.filter positivePredicate)) _ ?_ ?_
    · apply listQSum_congr_on
      intro left hleft
      exact hinner left (List.mem_filter.mp hleft).1
    · apply listQSum_filter_eq_of_zero_local
      intro left hleft hfalse
      have hnot :
          ¬ (0 : Q') <
            centralPhysicalRowMarginal
              w hw K half left := by
        simpa only [positivePredicate,
          decide_eq_false_iff_not] using hfalse
      apply listQSum_eqv_zero_of_all_local
      intro right hright
      have hentry :
          centralNormalizedPhysicalReflectedKernel
              w hw K half left right ≈ 0 :=
        centralNormalizedPhysicalReflectedKernel_eqv_zero_of_row_not_pos
          hright hnot
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (observable left * observable right) _ _ hentry)
        (Q'.mul_zero_eqv _)
  have hnormalize :
      listQSum
          (fun left => listQSum (term left) states)
          states ≈
        centralPhysicalReflectionQuadratic
            w K half observable * reciprocal := by
    refine Q'.eqv_trans _
      (listQSum
        (fun left =>
          listQSum (rawTerm left) states * reciprocal)
        states) _ ?_ ?_
    · apply listQSum_congr
      intro left
      refine Q'.eqv_trans _
        (listQSum
          (fun right => rawTerm left right * reciprocal)
          states) _ ?_ ?_
      · apply listQSum_congr
        intro right
        exact Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (observable left * observable right)
            (centralPhysicalReflectedKernel
              w K half left right)
            reciprocal)
      · exact listQSum_mul_right
          (rawTerm left) reciprocal states
    · exact Q'.eqv_trans _ _ _
        (listQSum_mul_right
          (fun left => listQSum (rawTerm left) states)
          reciprocal states)
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.eqv_refl _))
  refine Q'.eqv_trans _ _ _ hfiltered
    (Q'.eqv_trans _ _ _ hnormalize ?_)
  unfold centralNormalizedFullPhysicalReflectionQuadratic Q'.divPos reciprocal
  exact Q'.mul_eqv_congr_right _ _ _
    (centralPhysicalReflectionQuadratic_eq_full
      w K half observable)

/-! ## 2. Certificate-independent exact/physical same-action seam -/

/-- The literal exact all-cutoff Haar-network quadratic, with no reference
operator or spectral certificate in its definition.  The carrier is the
full bounded physical holonomy carrier, not the auxiliary positive-Haar
filter used by the grouped comparison.  The closed exact-normalization
theorem says that the displayed raw kernel already has vacuum partition
one. -/
def exactSlabAllCutoffQuadratic
    (w : Q') (K : Nat)
    (observable : EdgeLabelling → Q') : Q' :=
  finiteJointQuadratic
    (centralHalfStates K 0)
    observable
    (exactCorrectedSlabReflectedKernel w K 0)

/-- Named finite-scale same-action input from the signed exact Haar network
to the positive physical reflection law.  The target automatically has the
Perron positive-row presentation by
`centralPhysicalJointQuadratic_eq_normalizedFull`.

This is `Type`-level data so an eventual constructive proof retains the
identification as an explicit witness. -/
structure ExactHaarPhysicalPerronSameActionAt
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Type where
  same_action :
    ∀ observable,
      exactSlabAllCutoffQuadratic w K observable ≈
        centralNormalizedFullPhysicalReflectionQuadratic
          w hw K 0 observable

namespace ExactHaarPhysicalPerronSameActionAt

/-- The same-action witness lands directly on the filtered Perron joint. -/
theorem exact_eq_physicalJoint
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (identification :
      ExactHaarPhysicalPerronSameActionAt w hw K)
    (observable : EdgeLabelling → Q') :
    exactSlabAllCutoffQuadratic w K observable ≈
      centralPhysicalJointQuadratic
        w hw K 0 observable :=
  Q'.eqv_trans _ _ _
    (identification.same_action observable)
    (Q'.eqv_symm
      (centralPhysicalJointQuadratic_eq_normalizedFull
        w hw K 0 observable))

/-- Exact finite OS positivity transfers without any grouped-Mehler spectral
certificate once the same-action witness is supplied. -/
theorem exact_quadratic_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (identification :
      ExactHaarPhysicalPerronSameActionAt w hw K)
    (observable : EdgeLabelling → Q') :
    (0 : Q') ≤ exactSlabAllCutoffQuadratic w K observable := by
  exact Q'.le_trans' _ _ _
    (centralNormalizedFullPhysicalReflectionQuadratic_nonnegative
      w hw K 0 observable)
    (Q'.ge_of_eqv
      (identification.same_action observable))

/-- Unit normalization also transfers across the same finite identification. -/
theorem exact_quadratic_one
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (identification :
      ExactHaarPhysicalPerronSameActionAt w hw K) :
    exactSlabAllCutoffQuadratic w K (fun _ => 1) ≈ 1 :=
  Q'.eqv_trans _ _ _
    (identification.same_action (fun _ => 1))
    (centralNormalizedFullPhysicalReflectionQuadratic_one
      w hw K 0)

/-- Direct route around the Haar-centered truncated Gram: a physical
Perron/symmetric-reference comparison whose total rate is at most `1/4`
gives the literal exact-slab quarter contraction on the physical mean-zero
carrier. -/
theorem exact_quadratic_abs_le_quarter_of_physicalPerron
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (identification :
      ExactHaarPhysicalPerronSameActionAt w hw K)
    (comparison :
      CentralPhysicalSymmetricReferenceComparison
        w hw K 0)
    (hquarter :
      comparison.reference.rate + comparison.epsilon ≤
        Q'.mkPos 1 4 (by decide))
    (observable : EdgeLabelling → Q')
    (hmean : CentralPhysicalMeanZero w hw K 0 observable) :
    Q'.abs (exactSlabAllCutoffQuadratic w K observable) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          w hw K 0 observable observable := by
  have hphysical :=
    comparison.physical_markov_quadratic_abs_le_quarter
      hquarter observable hmean
  have hforms :
      exactSlabAllCutoffQuadratic w K observable ≈
        centralPhysicalWeightedInner w hw K 0
          observable
          (centralPhysicalMarkovApply
            w hw K 0 observable) :=
    Q'.eqv_trans _ _ _
      (identification.exact_eq_physicalJoint observable)
      (Q'.eqv_symm
        (centralPhysicalWeightedMarkovQuadratic_eq_joint
          w hw K 0 observable))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hforms))
    hphysical

/-- The direct gluing reroute.  Exact all-word gluing of a genuine local
stationary density and a local quarter contraction give a physical
centered-row sixteenth.  Symmetry turns that row estimate into a quadratic
estimate, and the same-action witness transfers it to the literal signed
Haar network.  No macro-slab reference operator, spectral eighth, row-error
eighth, or carrier-growth estimate occurs in this theorem. -/
theorem exact_quadratic_abs_le_sixteenth_of_local_gluing
    {w : Q'} {hw : (0 : Q') ≤ w} {K depth : Nat}
    {qS : Q'}
    (identification :
      ExactHaarPhysicalPerronSameActionAt w hw K)
    (qS_le_quarter :
      qS ≤
        YMGap.Continuum.FiveHolonomyPerronCutoff.quarter)
    (localRow_exists :
      ∀ source,
        source ∈ centralPositiveHalfStates w hw K 0 →
          Nonempty
            (Σ oneStep : EdgeLabelling → EdgeLabelling → Q',
              PhysicalBF4LocalContractionGluingRow
                hw K 0 source depth oneStep qS))
    (observable : EdgeLabelling → Q')
    (hmean : CentralPhysicalMeanZero w hw K 0 observable) :
    Q'.abs (exactSlabAllCutoffQuadratic w K observable) ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalWeightedInner
          w hw K 0 observable observable := by
  let states := centralPositiveHalfStates w hw K 0
  let physical :=
    centralNormalizedPhysicalReflectedKernel w hw K 0
  let vacuum := centralPhysicalVacuumJoint w hw K 0
  let physicalQuadratic :=
    finiteJointQuadratic states observable physical
  let vacuumQuadratic :=
    finiteJointQuadratic states observable vacuum
  have hvacuum : vacuumQuadratic ≈ 0 := by
    exact centralPhysicalVacuumJoint_quadratic_meanZero
      observable hmean
  have hdifference :
      physicalQuadratic + (-vacuumQuadratic) ≈
        physicalQuadratic := by
    exact Q'.eqv_trans _
      (physicalQuadratic + 0) _
      (Q'.add_eqv_congr_left
        physicalQuadratic (-vacuumQuadratic) 0
        (Q'.eqv_trans _ (-0) _
          (Q'.neg_eqv_congr _ _ hvacuum)
          (Q'.eqv_refl 0)))
      (Q'.eqv_of_eq
        (Q'.add_zero' physicalQuadratic))
  have hrow :
      ∀ state,
        state ∈ states →
          finiteJointDifferenceAbsRowMass
              states physical vacuum state ≤
            Q'.mkPos 1 16 (by decide) *
              centralPhysicalRowMarginal
                w hw K 0 state := by
    intro state hstate
    obtain ⟨⟨oneStep, row⟩⟩ :=
      localRow_exists state hstate
    change physicalCenteredPhysicalRowMass
        w hw K 0 state ≤ _
    exact row.physical_centered_row_le_sixteenth
      qS_le_quarter
  have hperturbation :
      Q'.abs
          (physicalQuadratic + (-vacuumQuadratic)) ≤
        Q'.mkPos 1 16 (by decide) *
          finiteWeightedSquare
            states
            (centralPhysicalRowMarginal w hw K 0)
            observable := by
    exact finiteJointQuadratic_abs_sub_le_weightedSquare
      states observable
      (centralPhysicalRowMarginal w hw K 0)
      physical vacuum
      (Q'.mkPos 1 16 (by decide))
      (fun left right hleft hright =>
        centralNormalizedPhysicalReflectedKernel_symm
          ((mem_centralPositiveHalfStates_iff).1 hleft).1
          ((mem_centralPositiveHalfStates_iff).1 hright).1)
      (fun left right _ _ =>
        centralPhysicalVacuumJoint_symmetric
          w hw K 0 left right)
      hrow
  have hphysical :
      Q'.abs physicalQuadratic ≤
        Q'.mkPos 1 16 (by decide) *
          centralPhysicalWeightedInner
            w hw K 0 observable observable := by
    refine Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (Q'.abs_eqv_congr hdifference))
      (Q'.le_trans' _ _ _ hperturbation ?_)
    exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_left
        (Q'.mkPos 1 16 (by decide))
        (finiteWeightedSquare
          states
          (centralPhysicalRowMarginal w hw K 0)
          observable)
        (centralPhysicalWeightedInner
          w hw K 0 observable observable)
        (finiteWeightedSquare_physical_eqv_inner
          w hw K 0 observable))
  have hforms :
      exactSlabAllCutoffQuadratic w K observable ≈
        physicalQuadratic := by
    exact identification.exact_eq_physicalJoint observable
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hforms))
    hphysical

/-- The direct gluing reroute in the exact quarter form expected by the
downstream slab consumer.  It is an immediate weakening of the proved
sixteenth. -/
theorem exact_quadratic_abs_le_quarter_of_local_gluing
    {w : Q'} {hw : (0 : Q') ≤ w} {K depth : Nat}
    {qS : Q'}
    (identification :
      ExactHaarPhysicalPerronSameActionAt w hw K)
    (qS_le_quarter :
      qS ≤
        YMGap.Continuum.FiveHolonomyPerronCutoff.quarter)
    (localRow_exists :
      ∀ source,
        source ∈ centralPositiveHalfStates w hw K 0 →
          Nonempty
            (Σ oneStep : EdgeLabelling → EdgeLabelling → Q',
              PhysicalBF4LocalContractionGluingRow
                hw K 0 source depth oneStep qS))
    (observable : EdgeLabelling → Q')
    (hmean : CentralPhysicalMeanZero w hw K 0 observable) :
    Q'.abs (exactSlabAllCutoffQuadratic w K observable) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          w hw K 0 observable observable := by
  have hsixteenth :=
    identification.exact_quadratic_abs_le_sixteenth_of_local_gluing
      qS_le_quarter localRow_exists observable hmean
  have hinner :
      (0 : Q') ≤
        centralPhysicalWeightedInner
          w hw K 0 observable observable := by
    unfold centralPhysicalWeightedInner
    apply listQSum_nonnegative_on
    intro state _
    exact Q'.mul_nonneg _ _
      (centralPhysicalRowMarginal_nonnegative
        hw K 0 state)
      (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
        (observable state))
  exact Q'.le_trans' _ _ _ hsixteenth
    (Q'.mul_le_mul_of_nonneg_right
      (Q'.mkPos 1 16 (by decide))
      (Q'.mkPos 1 4 (by decide))
      (centralPhysicalWeightedInner
        w hw K 0 observable observable)
      (by decide) hinner)

end ExactHaarPhysicalPerronSameActionAt

/-! ## 3. AF-family reroute -/

/-- AF-uniform exact/physical Perron route with no grouped feature-Gram
orders.  The analytic producer supplies a same-action witness and a physical
symmetric-reference comparison at each scale. -/
structure ExactHaarPhysicalPerronAFQuarterCertificate
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q') : Type where
  coupling_pos : ∀ scale, (0 : Q') < coupling scale
  coupling_le_window : ∀ scale, coupling scale ≤ law.g₁
  sameAction :
    ∀ scale,
      ExactHaarPhysicalPerronSameActionAt
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
  comparison :
    ∀ scale,
      CentralPhysicalSymmetricReferenceComparison
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
  rate_add_error_le_quarter :
    ∀ scale,
      (comparison scale).reference.rate +
          (comparison scale).epsilon ≤
        Q'.mkPos 1 4 (by decide)

namespace ExactHaarPhysicalPerronAFQuarterCertificate

/-- The AF family closes the literal exact-slab quarter at each scale on
the physical stationary-mean-zero carrier. -/
theorem exact_quadratic_abs_le_quarter_at
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      ExactHaarPhysicalPerronAFQuarterCertificate
        family law spacing coupling)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
        observable) :
    Q'.abs
        (exactSlabAllCutoffQuadratic
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          observable) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          observable observable :=
  (certificate.sameAction scale)
    |>.exact_quadratic_abs_le_quarter_of_physicalPerron
      (certificate.comparison scale)
      (certificate.rate_add_error_le_quarter scale)
      observable hmean

end ExactHaarPhysicalPerronAFQuarterCertificate

/-! ## 4. AF-family local-gluing bypass -/

/-- Minimal AF-uniform data for the direct bypass.  Unlike the grouped
spectral certificate, it contains no reference orders, feature Gram,
entrywise error, or carrier-growth budget.  Its only analytic input after
same action is the genuine one-slice stationary gluing witness with local
rate at most one quarter. -/
structure ExactHaarPhysicalLocalGluingAFQuarterCertificate
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q') : Type where
  coupling_pos : ∀ scale, (0 : Q') < coupling scale
  coupling_le_window : ∀ scale, coupling scale ≤ law.g₁
  sameAction :
    ∀ scale,
      ExactHaarPhysicalPerronSameActionAt
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
  depth : Nat → Nat
  localRate : Nat → Q'
  localRate_le_quarter :
    ∀ scale,
      localRate scale ≤
        YMGap.Continuum.FiveHolonomyPerronCutoff.quarter
  localRow_exists :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0 →
        Nonempty
          (Σ oneStep : EdgeLabelling → EdgeLabelling → Q',
            PhysicalBF4LocalContractionGluingRow
              (matchedAllSpinWeight_nonnegative
                family coupling scale)
              (matchedAllSpinCutoff family coupling scale) 0
              source (depth scale) oneStep
              (localRate scale))

namespace ExactHaarPhysicalLocalGluingAFQuarterCertificate

/-- The AF direct route gives a literal exact-slab sixteenth at every
matched scale, hence in particular the requested quarter contraction. -/
theorem exact_quadratic_abs_le_sixteenth_at
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      ExactHaarPhysicalLocalGluingAFQuarterCertificate
        family law spacing coupling)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
        observable) :
    Q'.abs
        (exactSlabAllCutoffQuadratic
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          observable) ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          observable observable :=
  (certificate.sameAction scale)
    |>.exact_quadratic_abs_le_sixteenth_of_local_gluing
      (certificate.localRate_le_quarter scale)
      (certificate.localRow_exists scale)
      observable hmean

/-- Exact quarter contraction in the standard downstream shape, obtained
without constructing the grouped macro-slab spectral/error certificate. -/
theorem exact_quadratic_abs_le_quarter_at
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      ExactHaarPhysicalLocalGluingAFQuarterCertificate
        family law spacing coupling)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
        observable) :
    Q'.abs
        (exactSlabAllCutoffQuadratic
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          observable) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          observable observable :=
  (certificate.sameAction scale)
    |>.exact_quadratic_abs_le_quarter_of_local_gluing
      (certificate.localRate_le_quarter scale)
      (certificate.localRow_exists scale)
      observable hmean

end ExactHaarPhysicalLocalGluingAFQuarterCertificate

end YMGap.Continuum.BF4ExactPhysicalPerronReroute

#print axioms YMGap.Continuum.BF4ExactPhysicalPerronReroute.centralPhysicalJointQuadratic_eq_normalizedFull
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronReroute.ExactHaarPhysicalPerronSameActionAt.exact_eq_physicalJoint
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronReroute.ExactHaarPhysicalPerronSameActionAt.exact_quadratic_nonnegative
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronReroute.ExactHaarPhysicalPerronSameActionAt.exact_quadratic_one
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronReroute.ExactHaarPhysicalPerronSameActionAt.exact_quadratic_abs_le_quarter_of_physicalPerron
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronReroute.ExactHaarPhysicalPerronSameActionAt.exact_quadratic_abs_le_sixteenth_of_local_gluing
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronReroute.ExactHaarPhysicalPerronSameActionAt.exact_quadratic_abs_le_quarter_of_local_gluing
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronReroute.ExactHaarPhysicalPerronAFQuarterCertificate.exact_quadratic_abs_le_quarter_at
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronReroute.ExactHaarPhysicalLocalGluingAFQuarterCertificate.exact_quadratic_abs_le_sixteenth_at
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronReroute.ExactHaarPhysicalLocalGluingAFQuarterCertificate.exact_quadratic_abs_le_quarter_at
